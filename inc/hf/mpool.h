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
struct mpool_entry;

struct mpool {
	struct spinlock lock;
	size_t entry_size;
	struct mpool_chunk *chunk_list;
	struct mpool_entry *entry_list;
	struct mpool *fallback;
};

/*@

// An unitialized mpool has these fields
predicate mpool_raw(struct mpool *p;) =
    p->entry_size     |-> _
    &*& p->chunk_list |-> _
    &*& p->entry_list |-> _
    &*& p->fallback   |-> _
    ;

predicate_ctor mpool_invariant(struct mpool *p)() =
    p->entry_size     |-> _
    &*& p->chunk_list |-> 0
    &*& p->entry_list |-> 0
    &*& p->fallback   |-> 0
    &*& spinlock(&p->lock, _)
    ;

predicate mpool(struct mpool *p) = mpool_invariant(p)();

@*/

void mpool_enable_locks(void);
	//@ requires true;
	//@ ensures true;

void mpool_init(struct mpool *p, size_t entry_size);
	//@ requires mpool_raw(p);
	//@ ensures mpool(p);

void mpool_init_from(struct mpool *p, struct mpool *from);
	//@ requires true;
	//@ ensures true;

void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback);
	//@ requires true;
	//@ ensures true;

void mpool_fini(struct mpool *p);
	//@ requires true;
	//@ ensures true;

bool mpool_add_chunk(struct mpool *p, void *begin, size_t size);
	//@ requires true;
	//@ ensures true;

void *mpool_alloc(struct mpool *p);
	//@ requires true;
	//@ ensures true;

void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align);
	//@ requires true;
	//@ ensures true;

void mpool_free(struct mpool *p, void *ptr);
	//@ requires true;
	//@ ensures true;

#endif
