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

struct mpool_chunk;
//@ predicate mpool_chunk_raw(struct mpool_chunk* c, void *limit;);
//@ predicate mpool_chunk(struct mpool_chunk* c, size_t ez; size_t size, int length);
struct mpool_entry;
//@ predicate mpool_entry_raw(struct mpool_entry* e, size_t size;);
//@ predicate mpool_entry(struct mpool_entry* e, size_t size; int length);

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
//	&*& p->lock       |-> _
	&*& p->entry_size |-> _
	&*& p->chunk_list |-> _
	&*& p->entry_list |-> _
	&*& p->fallback   |-> _
	;

predicate mpool(struct mpool *p; int entry_size, int chunks, int entries, struct mpool *fallback) = 
	p == NULL ? entry_size == 0 &*& chunks == 0 &*& entries == 0 &*& fallback == NULL
	:	
//		&*& p->lock       |-> ?lock
		    p->entry_size |-> ?ez
		&*& p->chunk_list |-> ?chunk
		&*& p->entry_list |-> ?entry
		&*& p->fallback   |-> fallback
		&*& entry_size == ez
		&*& ez >= 2*sizeof(void*)
		&*& mpool_chunk(chunk, entry_size, _, chunks)
		&*& mpool_entry(entry, entry_size, entries)
		//&*& [_]mpool(fallback, ez, _, _, _)
	;

// mpool_invariant(p)();

@*/

void mpool_enable_locks(void);
	//@ requires true;
	//@ ensures true;

void mpool_init(struct mpool *p, size_t entry_size);
	//@ requires p != 0 &*& mpool_raw(p) &*& entry_size > 2*sizeof(void*);
	//@ ensures mpool(p, entry_size, 0, 0, NULL);

void mpool_init_from(struct mpool *p, struct mpool *from);
	/*@
	requires p != 0
		&*& mpool_raw(p)
		&*& from != 0
		&*& mpool(from, ?ez, ?cs, ?es, ?fb)
	;
	@*/
	//@ ensures mpool(p, ez, cs, es, fb) &*& mpool(from, ez, 0, 0, NULL);

void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback);
	/*@
	requires p != 0
		&*& mpool_raw(p)
		&*& fallback != 0
		&*& [_]mpool(fallback, ?ez, ?cs, ?es, ?fb)
	;
	@*/
	//@ ensures mpool(p, ez, 0, 0, fallback) &*& [_]mpool(fallback, ez, cs, es, fb);

void mpool_fini(struct mpool *p);
	//@ requires p != 0 &*& mpool(p, ?ez, ?cs, ?es, ?fb) &*& mpool(fb, ez, ?fcs, ?fes, ?ffb);
	/*@
	ensures
		fb == NULL ? mpool(p, ez, cs, es, fb)
			&*& mpool(fb, ez, fcs, fes, ffb)
		: mpool(p, ez, 0, 0, NULL)
			&*& mpool(fb, ez, fcs + cs, fes + es, ffb)
	;
	@*/

bool mpool_add_chunk(struct mpool *p, void *begin, size_t size);
	/*@ requires
		p != NULL
		&*& mpool(p, ?ez, ?cs, ?es, ?fb)
		&*& begin != 0
		&*& mpool_chunk_raw(begin, begin + size)
		&*& size >= sizeof(struct mpool_chunk)
		&*& divrem(size, ez, ?q, 0)
		;
	@*/
	/*@ ensures
		result ? mpool(p, ez, cs + 1, es, fb)
		:	mpool(p, ez, cs, es, fb)
			&*& mpool_chunk_raw(begin, begin + size)
			&*& divrem(size, ez, q, 0)
		;
	@*/

void *mpool_alloc(struct mpool *p);
	//@ requires p != NULL &*& mpool(p, ?ez, ?cs, ?es, ?fb);
	/*@
		ensures 
			mpool(p, ez, _, _, fb)
			&*& result != NULL ? chars(result, ez, _) : true
		;
	@*/


void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align);
	//@ requires true;
	//@ ensures true;

void mpool_free(struct mpool *p, void *ptr);
	//@ requires p != NULL &*& mpool(p, ?ez, ?cs, ?es, ?fb) &*& ptr != 0 &*& mpool_entry_raw(ptr, ez);
	//@ ensures mpool(p, ez, cs, es + 1, fb);

#endif
