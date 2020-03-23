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

#include "hf/mpool.h"

#include <stdbool.h>

struct mpool_chunk {
	struct mpool_chunk *next_chunk;
	struct mpool_chunk *limit;
};
/*@
predicate mpool_chunk_raw(struct mpool_chunk* chunk, void *limit;) =
	chunk != NULL
	&*& chunk->next_chunk |-> _
	&*& chunk->limit      |-> _
	&*& struct_mpool_chunk_padding(chunk)
	&*& chars((void*)chunk + sizeof(struct mpool_chunk), limit - (void*)chunk - sizeof(struct mpool_chunk), _)
	;

predicate mpool_chunk(struct mpool_chunk* chunk;) =
	chunk != NULL
	&*& chunk->next_chunk |-> ?next
	&*& chunk->limit      |-> ?limit
	&*& struct_mpool_chunk_padding(chunk)
	&*& chars((void*)chunk + sizeof(struct mpool_chunk), (void*)limit - (void*)chunk - sizeof(struct mpool_chunk), _)
	&*& (next != NULL ? mpool_chunk(next) : true)
	&*& divrem((void*)limit - (void*)chunk, MPOOL_ENTRY_SIZE, ?q, 0)
	;

// TODO: prove this
lemma void divrem_pos();
    requires divrem(?D, ?d, ?q, 0) &*& D > 0 &*& d > 0;
    ensures divrem(D, d, q, 0) &*& D >= d;

lemma void divrem_pos2();
    requires divrem(?D, ?d, ?q, 0) &*& D > 0 &*& d > 0;
    ensures divrem(D - d, d, _, 0);

@*/

struct mpool_entry {
	struct mpool_entry *next;
};
/*@	
predicate mpool_entry_raw(struct mpool_entry* entry;) =
	entry != NULL
	&*& entry->next |-> _
	&*& struct_mpool_entry_padding(entry)
	&*& chars((void*)entry + sizeof(struct mpool_entry), MPOOL_ENTRY_SIZE - sizeof(struct mpool_entry), _)
	;

predicate mpool_entry(struct mpool_entry* entry;) =
	entry != NULL
	&*& entry->next |-> ?next
	&*& struct_mpool_entry_padding(entry)
	&*& chars((void*)entry + sizeof(struct mpool_entry), MPOOL_ENTRY_SIZE - sizeof(struct mpool_entry), _)
	&*& (next != NULL ? mpool_entry(next) : true)
	;
@*/

static bool mpool_locks_enabled = false;

/**
 * Enables the locks protecting memory pools. Before this function is called,
 * the locks are disabled, that is, acquiring/releasing them is a no-op.
 */
void mpool_enable_locks(void)
	//@ requires true;
	//@ ensures true;
{
	//@ assume(false);	
	mpool_locks_enabled = true;
}

/**
 * Acquires the lock protecting the given memory pool, if locks are enabled.
 */
static void mpool_lock(struct mpool *p)
	//@ requires p != 0 &*& [_]mpool(p, ?non_empty, ?have_fb);
	//@ ensures [1]mpool(p, non_empty, have_fb);
{
	//@ assume(false);
	if (mpool_locks_enabled) {
		sl_lock(&p->lock);
	}
	// leak [_]mpool(fb, _, _);
}

/**
 * Releases the lock protecting the given memory pool, if locks are enabled.
 */
static void mpool_unlock(struct mpool *p)
	//@ requires p != 0 &*& mpool(p, ?non_empty, ?have_fb);
	//@ ensures [_]mpool(p, non_empty, have_fb);
{
	//@ assume(false);
	if (mpool_locks_enabled) {
		sl_unlock(&p->lock);
	}
}

/**
 * Initialises the given memory pool with the given entry size, which must be
 * at least the size of two pointers.
 *
 * All entries stored in the memory pool will be aligned to at least the entry
 * size.
 */
void mpool_init(struct mpool *p, size_t entry_size)
	//@ requires p != 0 &*& mpool_raw(p) &*& entry_size == MPOOL_ENTRY_SIZE;
	/*@
	ensures
		mpool(p, false, false)
	;
	@*/
{
	p->entry_size = entry_size;
	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;
//	sl_init(&p->lock);
}

/**
 * Initialises the given memory pool by replicating the properties of `from`. It
 * also pulls the chunk and free lists from `from`, consuming all its resources
 * and making them available via the new memory pool.
 */
void mpool_init_from(struct mpool *p, struct mpool *from)
	/*@
	requires p != 0
		&*& mpool_raw(p)
		&*& from != 0
		&*& [_]mpool(from, ?non_empty, ?have_fb)
	;
	@*/
	//@ ensures mpool(p, non_empty, have_fb) &*& [_]mpool(from, false, false);
{
	mpool_init(p, from->entry_size);

	mpool_lock(from);
	//@ open [1]mpool(from, _, _);
	p->chunk_list = from->chunk_list;
	p->entry_list = from->entry_list;
	p->fallback = from->fallback;

	from->chunk_list = NULL;
	from->entry_list = NULL;
	from->fallback = NULL;
	
	mpool_unlock(from);
}

/**
 * Initialises the given memory pool with a fallback memory pool if this pool
 * runs out of memory.
 */
void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback)
	/*@
	requires p != 0
		&*& mpool_raw(p)
		&*& fallback != 0
		&*& [_]mpool(fallback, ?non_empty, ?have_fb)
	;
	@*/
	//@ ensures mpool(p, false, true) &*& [_]mpool(fallback, non_empty, have_fb);
{
	mpool_init(p, fallback->entry_size);
	p->fallback = fallback;
}

/**
 * Finishes the given memory pool, giving all free memory to the fallback pool
 * if there is one.
 */
void mpool_fini(struct mpool *p)
	/*@
	requires 
		p != 0 
		&*& [_]mpool(p, ?non_empty, ?have_fb)
		;
	@*/
	/*@
	ensures
		have_fb ? [_]mpool(p, false, false) : [_]mpool(p, non_empty, have_fb)
		;
	@*/
{
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

	if (!p->fallback) {
		return;
	}
		
	mpool_lock(p);
	
	// open mpool(p, non_empty, have_fb);
	// assert(p->fallback |-> ?fb);
	// assert(fb != NULL);

	/* Merge the freelist into the fallback. */
	entry = p->entry_list;
	int c = 0;
	while (entry != NULL) 
		//@ invariant p->fallback |-> ?fb &*& fb != NULL &*& [_]mpool(fb, _, _) &*& (entry != NULL ? mpool_entry(entry) : true);
	{
		void *ptr = entry;

		entry = entry->next;
		mpool_free(p->fallback, ptr);
		++c;
	}
	// open mpool_entry(entry, _);
	// assert(c == es);

	/* Merge the chunk list into the fallback. */
	chunk = p->chunk_list;
	c = 0;
	while (chunk != NULL) 
		//@ invariant p->fallback |-> fb &*& [_]mpool(fb, _, _) &*& (chunk != NULL ? mpool_chunk(chunk) : true);
	{
		//@ open mpool_chunk(chunk);

		void *ptr = chunk;
		size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk;

		chunk = chunk->next_chunk;
		//@ close mpool_chunk_raw(ptr, ptr + size);
		bool res = mpool_add_chunk(p->fallback, ptr, size);
		if (!res) { 
			//@ assume(false); 
		}
		++c;
	}

	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;
	// close mpool_chunk(0, ez, 0, 0);
	// close mpool_entry(0, ez, 0);
	// close mpool(p, ez, 0, 0, NULL);

	mpool_unlock(p);
}

/**
 * Adds a contiguous chunk of memory to the given memory pool. The chunk will
 * eventually be broken up into entries of the size held by the memory pool.
 *
 * Only the portions aligned to the entry size will be added to the pool.
 *
 * Returns true if at least a portion of the chunk was added to pool, or false
 * if none of the buffer was usable in the pool.
 */
bool mpool_add_chunk(struct mpool *p, void *begin, size_t size)
	/*@ requires
		p != NULL
		&*& [_]mpool(p, ?non_empty, ?have_fb)
		&*& begin != 0
		&*& mpool_chunk_raw(begin, begin + size)
		&*& size >= sizeof(struct mpool_chunk)
		&*& divrem(size, MPOOL_ENTRY_SIZE, ?q, 0)
		;
	@*/
	/*@ ensures
		result ? [_]mpool(p, true, have_fb)
		:	[_]mpool(p, non_empty, have_fb)
			&*& mpool_chunk_raw(begin, begin + size)
			&*& divrem(size, MPOOL_ENTRY_SIZE, q, 0)

		;
	@*/
{
	struct mpool_chunk *chunk;
	uintptr_t new_begin;
	uintptr_t new_end;

	/* Round begin address up, and end address down. */
	new_begin = (uintptr_t)begin;/*((uintptr_t)begin + p->entry_size - 1) / p->entry_size *
		    p->entry_size;*/
	new_end = ((uintptr_t)begin + size);// / p->entry_size * p->entry_size;
	
	/* Nothing to do if there isn't enough room for an entry. */
	if (new_begin >= new_end || new_end - new_begin < p->entry_size) {
		return false;
	}

	chunk = (struct mpool_chunk *)new_begin;
	chunk->limit = (struct mpool_chunk *)new_end;

	mpool_lock(p);
	//@ open mpool(p, _, _);
	chunk->next_chunk = p->chunk_list;
	// open mpool_chunk(p->chunk_list);
	// close mpool_chunk(p->chunk_list);
	// close mpool_chunk(chunk, ez, _, cs + 1);
	p->chunk_list = chunk;
	mpool_unlock(p);

	return true;
}

/**
 * Allocates an entry from the given memory pool, if one is available. The
 * fallback will not be used even if there is one.
 */
static void *mpool_alloc_no_fallback(struct mpool *p)
	//@ requires p != NULL &*& [_]mpool(p, ?non_empty, ?have_fb);
	//@ ensures [_]mpool(p, non_empty, have_fb) &*& (result != NULL ? chars(result, MPOOL_ENTRY_SIZE, _) : true);
{
	void *ret;
	struct mpool_chunk *chunk;
	struct mpool_chunk *new_chunk;

	/* Fetch an entry from the free list if one is available. */
	mpool_lock(p);
	//@ open mpool(p, _, _);
	if (p->entry_list != NULL) {
		// open mpool_entry(p->entry_list, ez, es);
		// close mpool_entry(p->entry_list, ez, es);
		// assert(es > 0);
		struct mpool_entry *entry = p->entry_list;

		p->entry_list = entry->next;
		//@ open_struct(entry);
		ret = entry;
		goto exit;
	}
	// open mpool_entry(p->entry_list);
	// close mpool_entry(p->entry_list);
	// assert(es == 0);

	/* There was no free list available. Try a chunk instead. */
	chunk = p->chunk_list;
	if (chunk == NULL) {
		/* The chunk list is also empty, we're out of entries. */
		// open mpool_chunk(chunk, _, _, _);
		// assert(cs == 0);
		ret = NULL;
		goto exit;
	}

	// open mpool_chunk(chunk, ez, ?size, cs);
	// close mpool_chunk(chunk, ez, size, cs);
	new_chunk = (struct mpool_chunk *)((uintptr_t)chunk + p->entry_size);
	if (new_chunk >= chunk->limit) {
		p->chunk_list = chunk->next_chunk;
		//@ open_struct(chunk);
		//@ chars_join((void*)chunk);
		//@ divrem_pos();
		//@ chars_split((void*)chunk, MPOOL_ENTRY_SIZE);
		// FIXME:
		//@ leak divrem(_,_,_,_);
		//@ leak chars((void*)chunk + MPOOL_ENTRY_SIZE, _, _);
	} else {
	//@ assert(chunk->limit |-> ?limit1);
	//@ assert(chunk->next_chunk |-> ?next_chunk1);
		//@ open_struct(chunk);
		//@ chars_join((void*)chunk);
		//@ chars_split((void*)chunk, p->entry_size);
	//@ assume(sizeof(struct mpool_chunk) <= MPOOL_ENTRY_SIZE);
		//@ chars_split((void*)chunk, sizeof(struct mpool_chunk));
		//@ close_struct(chunk);
	//@ assert(chunk->limit |-> ?limit2);
	//@ assert(chunk->next_chunk |-> ?next_chunk2);
	//@ assume(limit1 == limit2 && next_chunk1 == next_chunk2);
		
	//@ assume(sizeof(struct mpool_chunk) <= (void*)chunk->limit - (void*)chunk - MPOOL_ENTRY_SIZE);
		//@ chars_split((void*)new_chunk, sizeof(struct mpool_chunk));
		//@ close_struct(new_chunk);
		// *new_chunk = *chunk;
		new_chunk->limit = chunk->limit;
		new_chunk->next_chunk = chunk->next_chunk;
		p->chunk_list = new_chunk;
	//@ assume((void*)new_chunk->limit - (void*)new_chunk >= MPOOL_ENTRY_SIZE);
		//@ divrem_pos2();
		//@ close mpool_chunk(new_chunk);
		//@ close mpool(p, _, _);
		//@ open_struct(chunk);
		
	}

	ret = chunk;

exit:
	mpool_unlock(p);

	return ret;
}

/**
 * Allocates an entry from the given memory pool, if one is available. If there
 * isn't one available, try and allocate from the fallback if there is one.
 */
void *mpool_alloc(struct mpool *p)
	//@ requires p != NULL &*& [_]mpool(p, ?non_empty, ?have_fb);
	//@ ensures [_]mpool(p, non_empty, have_fb) &*& result != NULL ? chars(result, MPOOL_ENTRY_SIZE, _) : true;
{
	do
	//@ invariant p != NULL &*& [_]mpool(p, _, _);
	{
		void *ret = mpool_alloc_no_fallback(p);

		if (ret != NULL) {
			return ret;
		}

		p = p->fallback;
	} while (p != NULL);

	return NULL;
}

/**
 * Frees an entry back into the memory pool, making it available for reuse.
 *
 * This is meant to be used for freeing single entries. To free multiple
 * entries, one must call mpool_add_chunk instead.
 */
void mpool_free(struct mpool *p, void *ptr)
	//@ requires p != NULL &*& [_]mpool(p, ?non_empty, ?have_fb) &*& ptr != 0 &*& mpool_entry_raw(ptr);
	//@ ensures [_]mpool(p, true, have_fb);
{
	struct mpool_entry *e = ptr;

	/* Store the newly freed entry in the front of the free list. */
	mpool_lock(p);
	e->next = p->entry_list;
	p->entry_list = e;
	mpool_unlock(p);
}

/**
 * Allocates a number of contiguous and aligned entries. If a suitable
 * allocation could not be found, the fallback will not be used even if there is
 * one.
 */
void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count,
					 size_t align)
	// requires p != NULL &*& [_]mpool(p, ?non_empty, ?have_fb);
	/*
	ensures 
		[_]mpool(p, non_empty, have_fb)
		&*& result != NULL ? 
			chars(result, count, _) 
			&*& divrem((int)result, align, _, 0)
		    : true
	;
	@*/

{
	struct mpool_chunk **prev;
	void *ret = NULL;

	align *= p->entry_size;

	mpool_lock(p);

	/*
	 * Go through the chunk list in search of one with enough room for the
	 * requested allocation
	 */
	prev = &p->chunk_list;
	while (*prev != NULL) {
		uintptr_t start;
		struct mpool_chunk *new_chunk;
		struct mpool_chunk *chunk = *prev;

		/* Round start address up to the required alignment. */
		start = (((uintptr_t)chunk + align - 1) / align) * align;

		/*
		 * Calculate where the new chunk would be if we consume the
		 * requested number of entries. Then check if this chunk is big
		 * enough to satisfy the request.
		 */
		new_chunk =
			(struct mpool_chunk *)(start + (count * p->entry_size));
		if (new_chunk <= chunk->limit) {
			/* Remove the consumed area. */
			if (new_chunk == chunk->limit) {
				*prev = chunk->next_chunk;
			} else {
				*new_chunk = *chunk;
				*prev = new_chunk;
			}

			/*
			 * Add back the space consumed by the alignment
			 * requirement, if it's big enough to fit an entry.
			 */
			if (start - (uintptr_t)chunk >= p->entry_size) {
				chunk->next_chunk = *prev;
				*prev = chunk;
				chunk->limit = (struct mpool_chunk *)start;
			}

			ret = (void *)start;
			break;
		}

		prev = &chunk->next_chunk;
	}

	mpool_unlock(p);

	return ret;
}

/**
 * Allocates a number of contiguous and aligned entries. This is a best-effort
 * operation and only succeeds if such entries can be found in the chunks list
 * or the chunks of the fallbacks (i.e., the entry list is never used to satisfy
 * these allocations).
 *
 * The alignment is specified as the number of entries, that is, if `align` is
 * 4, the alignment in bytes will be 4 * entry_size.
 *
 * The caller can enventually free the returned entries by calling
 * mpool_add_chunk.
 */
void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align)
	// requires true;
	// ensures true;
{
	do {
		void *ret = mpool_alloc_contiguous_no_fallback(p, count, align);

		if (ret != NULL) {
			return ret;
		}

		p = p->fallback;
	} while (p != NULL);

	return NULL;
}
