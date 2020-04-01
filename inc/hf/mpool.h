/*
 * Copyright 2018 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//#pragma once
#ifdef HF_MPOOL_H
#else
#define HF_MPOOL_H

#include <stdbool.h>
#include <stddef.h>

#include "hf/spinlock.h"

//#include "hf/mm.h"
#define MPOOL_ENTRY_SIZE 256
//sizeof(struct mm_page_table)

struct mpool_chunk;
//@ predicate mpool_chunk_raw(struct mpool_chunk* c, void *limit;);
//@ predicate mpool_chunk(struct mpool_chunk* c;);
struct mpool_entry;
//@ predicate mpool_entry_raw(struct mpool_entry* e;);
//@ predicate mpool_entry(struct mpool_entry* e;);

struct mpool {
	struct spinlock lock;
	size_t entry_size;
	struct mpool_chunk *chunk_list;
	struct mpool_entry *entry_list;
	struct mpool *fallback;
};

/*@
predicate mpool_raw(struct mpool *p;) =
	p != NULL
	//&*& p->lock       |-> _
	&*& p->entry_size |-> _
	&*& p->chunk_list |-> _
	&*& p->entry_list |-> _
	&*& p->fallback   |-> _
	;

predicate mpool(struct mpool *p; bool non_empty, bool have_fb) =
	p != NULL 
	//&*& p->lock       |-> ?lock
	&*& p->entry_size |-> ?entry_size
	&*& p->chunk_list |-> ?chunk
	&*& p->entry_list |-> ?entry
	&*& p->fallback   |-> ?fallback
	&*& entry_size == MPOOL_ENTRY_SIZE
	&*& ((chunk == NULL && entry == NULL) ? non_empty == false 
	    :	non_empty == true
	    	&*& (chunk != NULL ? mpool_chunk(chunk) : true)
		&*& (entry != NULL ? mpool_entry(entry) : true)
	    )
	&*& (fallback == NULL ? have_fb == false
	    :	have_fb == true
	    	&*& [_]mpool(fallback, _, _)
	    )
	;
@*/

void mpool_enable_locks(void);

void mpool_init(struct mpool *p, size_t entry_size);
	//@ requires p != 0 &*& mpool_raw(p) &*& entry_size == MPOOL_ENTRY_SIZE;
	//@ ensures mpool(p, false, false);

void mpool_init_from(struct mpool *p, struct mpool *from);
	/*@
	requires p != 0
		&*& mpool_raw(p)
		&*& from != 0
		&*& [?f]mpool(from, ?non_empty, ?have_fb)
	;
	@*/
	//@ ensures mpool(p, non_empty, have_fb) &*& [f]mpool(from, false, false);

void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback);
	/*@
	requires p != 0
		&*& mpool_raw(p)
		&*& fallback != 0
		&*& [_]mpool(fallback, ?non_empty, ?have_fb)
	;
	@*/
	//@ ensures mpool(p, false, true);

void mpool_fini(struct mpool *p);
	//@ requires p != 0 &*& [?f]mpool(p, ?non_empty, ?have_fb);
	//@ ensures have_fb ? [f]mpool(p, false, false) : [f]mpool(p, non_empty, have_fb);

bool mpool_add_chunk(struct mpool *p, void *begin, size_t size);
	/*@ requires
		p != NULL
		&*& [?f]mpool(p, ?non_empty, ?have_fb)
		&*& begin != 0
		&*& chars(begin, size, _)
		&*& size >= sizeof(struct mpool_chunk)
		;
	@*/
	/*@ ensures
		result ? [f]mpool(p, true, have_fb)
		:	[f]mpool(p, non_empty, have_fb)
			&*& chars(begin, size, _)
		;
	@*/

void *mpool_alloc(struct mpool *p);
	//@ requires p != NULL &*& [?f]mpool(p, ?non_empty, ?have_fb);
	//@ ensures [f]mpool(p, _, have_fb) &*& result != NULL ? chars(result, MPOOL_ENTRY_SIZE, _) : true;


void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align);

void mpool_free(struct mpool *p, void *ptr);
	/*@
	requires
		p != NULL
		&*& [?f]mpool(p, ?non_empty, ?have_fb)
		&*& ptr != 0
		&*& chars(ptr, MPOOL_ENTRY_SIZE, _)
		;
	@*/
	//@ ensures [f]mpool(p, true, have_fb);

#endif
