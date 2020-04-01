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
	&*& divrem((uintptr_t)chunk, MPOOL_ENTRY_SIZE, ?chunk_q, 0)
	&*& divrem((uintptr_t)limit, MPOOL_ENTRY_SIZE, ?limit_q, 0)
	&*& limit_q > chunk_q
	;

predicate mpool_chunk(struct mpool_chunk* chunk;) =
	chunk != NULL
	&*& chunk->next_chunk |-> ?next
	&*& chunk->limit      |-> ?limit
	&*& struct_mpool_chunk_padding(chunk)
	&*& chars((void*)chunk + sizeof(struct mpool_chunk), (void*)limit - (void*)chunk - sizeof(struct mpool_chunk), _)
	&*& (next != NULL ? mpool_chunk(next) : true)
	&*& divrem((uintptr_t)chunk, MPOOL_ENTRY_SIZE, ?chunk_q, 0)
	&*& divrem((uintptr_t)limit, MPOOL_ENTRY_SIZE, ?limit_q, 0)
	&*& limit_q > chunk_q 
	;

// TODO: prove this
lemma void divrem_pos();
	requires divrem(?D, ?d, ?q, 0) &*& D > 0 &*& d > 0;
	ensures divrem(D, d, q, 0) &*& D >= d;

lemma void divrem_pos2();
	requires divrem(?D, ?d, ?q, 0) &*& D > 0 &*& d > 0;
	ensures divrem(D, d, q, 0) &*& divrem(D - d, d, _, 0);

lemma void divrem3(int D);
	requires divrem(D, ?d, ?q, ?r);
	ensures divrem(D, d, q, r) &*& divrem(D + d, d, q + 1, r);
	
lemma void divrem4(int D1, int D2);
	requires divrem(D1, ?d, ?q1, 0) &*& divrem(D2, d, ?q2, 0);
	ensures divrem(D1, d, q1, 0) &*& divrem(D2, d, q2, 0) &*& divrem(D1 + D2, d, q1 + q2, 0);

lemma void divrem5(int D1, int D2);
	requires divrem(D1, ?d, ?q1, 0) &*& divrem(D2, d, ?q2, 0) &*& D1 <= D2;
	ensures divrem(D1, d, q1, 0) &*& divrem(D2, d, q2, 0) &*& divrem(D2 - D1, d, q2 - q1, 0);
	
lemma void mpool_chunk_raw_of_chars(void *p)
	requires 
		p != NULL
		&*& chars(p, ?size, _)
		&*& size >= sizeof(struct mpool_chunk)
		&*& divrem((uintptr_t)p, MPOOL_ENTRY_SIZE, _, 0)
		&*& divrem(size, MPOOL_ENTRY_SIZE, ?size_q, 0)
		;
	ensures
		mpool_chunk_raw((struct mpool_chunk *)p, p + size)
		&*& divrem(size, MPOOL_ENTRY_SIZE, size_q, 0)
		;
{
	chars_split((void *)p, sizeof(struct mpool_chunk));
	close_struct((struct mpool_chunk *)p);
	divrem4((int)p, size);
}

lemma void mpool_chunk_split_entry(struct mpool_chunk *chunk)
	requires
		    chunk != NULL
		&*& chunk->next_chunk |-> ?next
		&*& chunk->limit      |-> ?limit
		&*& struct_mpool_chunk_padding(chunk)
		&*& chars((void *)chunk + sizeof(struct mpool_chunk), (void*)limit - (void*)chunk - sizeof(struct mpool_chunk), _)
		&*& (void*)limit - (void*)chunk >= MPOOL_ENTRY_SIZE
		;
	ensures 
		    chunk->next_chunk |-> next
		&*& chunk->limit      |-> limit
		&*& struct_mpool_chunk_padding(chunk)
		&*& chars((void *)chunk + sizeof(struct mpool_chunk), MPOOL_ENTRY_SIZE - sizeof(struct mpool_chunk), _)
		&*& chars((void *)chunk + MPOOL_ENTRY_SIZE, (void *)limit - (void *)chunk - MPOOL_ENTRY_SIZE, _)
		;
{	
	open_struct(chunk);
	chars_join((void *)chunk);
	chars_split((void *)chunk, MPOOL_ENTRY_SIZE);
	
	assume(sizeof(struct mpool_chunk) <= MPOOL_ENTRY_SIZE);
	chars_split((void *)chunk, sizeof(struct mpool_chunk));
	close_struct(chunk);
	
	// open_struct and close_struct don't track the content of the struct so we have to assume it here
	assert(chunk->limit |-> ?limit2);
	assert(chunk->next_chunk |-> ?next2);
	assume(limit == limit2 && next == next2);
}
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
	
lemma void mpool_entry_raw_of_chars(void *p)
	requires p != 0 &*& chars(p, MPOOL_ENTRY_SIZE, _);
	ensures mpool_entry_raw((struct mpool_entry *)p);
{
	assume(sizeof(struct mpool_entry) <= MPOOL_ENTRY_SIZE);
	chars_split(p, sizeof(struct mpool_entry));
	close_struct((struct mpool_entry *)p);
}
@*/

static bool mpool_locks_enabled = false;

/**
 * Enables the locks protecting memory pools. Before this function is called,
 * the locks are disabled, that is, acquiring/releasing them is a no-op.
 */
void mpool_enable_locks(void)
{
	mpool_locks_enabled = true;
}

/**
 * Acquires the lock protecting the given memory pool, if locks are enabled.
 */
/*@
predicate my_spinlock_held(struct mpool *p, real f);
@*/
static void mpool_lock(struct mpool *p)
	//@ requires p != NULL &*& [?f]mpool(p, ?non_empty, ?have_fb);
	//@ ensures mpool(p, non_empty, have_fb) &*& my_spinlock_held(p, f);
{
	//@ assume(false);
	if (mpool_locks_enabled) {
		sl_lock(&p->lock);
	}
}

/**
 * Releases the lock protecting the given memory pool, if locks are enabled.
 */
static void mpool_unlock(struct mpool *p)
	//@ requires p != 0 &*& mpool(p, ?non_empty, ?have_fb) &*& my_spinlock_held(p, ?f);
	//@ ensures [f]mpool(p, non_empty, have_fb);
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
	//@ ensures mpool(p, false, false);
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
		&*& [?f]mpool(from, ?non_empty, ?have_fb)
	;
	@*/
	//@ ensures mpool(p, non_empty, have_fb) &*& [f]mpool(from, false, false);
{
	mpool_init(p, from->entry_size);

	mpool_lock(from);
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
	//@ ensures mpool(p, false, true);
{
	mpool_init(p, fallback->entry_size);
	p->fallback = fallback;
}

/**
 * Finishes the given memory pool, giving all free memory to the fallback pool
 * if there is one.
 */
void mpool_fini(struct mpool *p)
	//@ requires p != 0 &*& [?f]mpool(p, ?non_empty, ?have_fb);
	//@ ensures have_fb ? [f]mpool(p, false, false) : [f]mpool(p, non_empty, have_fb);
{
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

	if (!p->fallback) {
		return;
	}
		
	mpool_lock(p);
	
	/* Merge the freelist into the fallback. */
	entry = p->entry_list;
	int c = 0;
	while (entry != NULL) 
		//@ invariant p->fallback |-> ?fb &*& fb != NULL &*& [_]mpool(fb, _, _) &*& (entry != NULL ? mpool_entry(entry) : true);
	{
		void *ptr = entry;

		entry = entry->next;
		//@ open_struct((struct mpool_entry *)ptr);
		mpool_free(p->fallback, ptr);
		++c;
	}

	/* Merge the chunk list into the fallback. */
	chunk = p->chunk_list;
	c = 0;
	while (chunk != NULL) 
		//@ invariant p->fallback |-> fb &*& [_]mpool(fb, _, _) &*& (chunk != NULL ? mpool_chunk(chunk) : true);
	{
		void *ptr = chunk;
		size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk;

		chunk = chunk->next_chunk;
		//@ open_struct((struct mpool_chunk *)ptr);
		bool res = mpool_add_chunk(p->fallback, ptr, size);
		// FIXME: the assume below relies on the leaked divrem
		//@ assume(res);
		//@ leak divrem(_, MPOOL_ENTRY_SIZE, _, 0);
		//@ leak divrem(_, MPOOL_ENTRY_SIZE, _, 0);
		
		++c;
	}

	p->chunk_list = NULL;
	p->entry_list = NULL;
	p->fallback = NULL;

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
		&*& [?f]mpool(p, ?non_empty, ?have_fb)
		&*& begin != 0
		&*& chars(begin, size, _)
		;
	@*/
	/*@ ensures
		result ? [f]mpool(p, true, have_fb)
		:	[f]mpool(p, non_empty, have_fb)
			&*& chars(begin, size, _)
		;
	@*/
{
	struct mpool_chunk *chunk;
	uintptr_t new_begin;
	uintptr_t new_end;

	/* Round begin address up, and end address down. */
	new_begin = ((uintptr_t)begin + p->entry_size - 1) / p->entry_size *
		    p->entry_size;
	// assume(new_begin == ((uintptr_t)begin % MPOOL_ENTRY_SIZE == 0 ? (uintptr_t)begin : (uintptr_t)begin + (MPOOL_ENTRY_SIZE - ((uintptr_t)begin % MPOOL_ENTRY_SIZE))));
	//@ assume(new_begin >= (uintptr_t)begin);
	//@ assume(new_begin == MPOOL_ENTRY_SIZE * (new_begin / MPOOL_ENTRY_SIZE));
	//@ divrem_intro(new_begin, MPOOL_ENTRY_SIZE, new_begin / MPOOL_ENTRY_SIZE, 0);
    
	new_end = ((uintptr_t)begin + size) / p->entry_size * p->entry_size;
	// assume(new_end == ((uintptr_t)begin + size) - (((uintptr_t)begin + size) % MPOOL_ENTRY_SIZE));
	//@ assume(new_end <= (uintptr_t)begin + size);
	//@ assume(new_end == MPOOL_ENTRY_SIZE * (new_end / MPOOL_ENTRY_SIZE));
	//@ divrem_intro(new_end, MPOOL_ENTRY_SIZE, new_end / MPOOL_ENTRY_SIZE, 0);

	/* Nothing to do if there isn't enough room for an entry. */
	if (new_begin >= new_end || new_end - new_begin < p->entry_size) {
		//@ leak divrem(new_begin, MPOOL_ENTRY_SIZE, new_begin / MPOOL_ENTRY_SIZE, 0);
		//@ leak divrem(new_end, MPOOL_ENTRY_SIZE, new_end / MPOOL_ENTRY_SIZE, 0);
		return false;
	}
	//@ divrem5(new_begin, new_end);
	
	chunk = (struct mpool_chunk *)new_begin;
	//@ chars_split(begin, (void *)new_begin - (void *)begin);
	//@ chars_split((void *)new_begin, (void *)new_end - (void *)new_begin);
	//@ assume(sizeof(struct mpool_chunk) <= MPOOL_ENTRY_SIZE);
	//@ mpool_chunk_raw_of_chars((void *)new_begin);
	chunk->limit = (struct mpool_chunk *)new_end;

	mpool_lock(p);
	chunk->next_chunk = p->chunk_list;
	// close mpool_chunk(chunk);
	p->chunk_list = chunk;
	mpool_unlock(p);

	//@ leak chars(begin, _, _);
	//@ leak chars((void *)new_end, _, _);
	//@ leak divrem(new_end, MPOOL_ENTRY_SIZE, _, 0);
	//@ leak divrem(new_end - new_begin, MPOOL_ENTRY_SIZE, _, 0);
	return true;
}

/**
 * Allocates an entry from the given memory pool, if one is available. The
 * fallback will not be used even if there is one.
 */
static void *mpool_alloc_no_fallback(struct mpool *p)
	//@ requires p != NULL &*& [?f]mpool(p, ?non_empty, ?have_fb);
	//@ ensures [f]mpool(p, _, have_fb) &*& (result != NULL ? chars(result, MPOOL_ENTRY_SIZE, _) : true);
{
	void *ret;
	struct mpool_chunk *chunk;
	struct mpool_chunk *new_chunk;

	/* Fetch an entry from the free list if one is available. */
	mpool_lock(p);
	if (p->entry_list != NULL) {
		struct mpool_entry *entry = p->entry_list;

		p->entry_list = entry->next;
		//@ open_struct(entry);
		ret = entry;
		goto exit;
	}

	/* There was no free list available. Try a chunk instead. */
	chunk = p->chunk_list;
	if (chunk == NULL) {
		/* The chunk list is also empty, we're out of entries. */
		ret = NULL;
		goto exit;
	}

	new_chunk = (struct mpool_chunk *)((uintptr_t)chunk + p->entry_size);
	if (new_chunk >= chunk->limit) {
		//@ assert(chunk->limit |-> ?limit);
		
		p->chunk_list = chunk->next_chunk;
		// mpool_chunk_to_chars(chunk);
		//@ open_struct(chunk);
		//@ chars_join((void*)chunk);
		//@ divrem_pos();

		//@ leak divrem((int)chunk, MPOOL_ENTRY_SIZE, _, 0);
		//@ leak divrem((int)limit, MPOOL_ENTRY_SIZE, _, 0);
	} else {
		//@ assert(chunk->limit |-> ?limit);
		
		//@ mpool_chunk_split_entry(chunk);
		//@ assume(sizeof(struct mpool_chunk) <= (void *)chunk->limit - (void *)chunk - MPOOL_ENTRY_SIZE);
		//@ divrem3((int)chunk);
		//@ divrem5((int)new_chunk, (int)chunk->limit);
		//@ mpool_chunk_raw_of_chars((void *)new_chunk);
		// DIFF: hf uses '*new_chunk = *chunk;'
		new_chunk->limit = chunk->limit;
		new_chunk->next_chunk = chunk->next_chunk;
		
		p->chunk_list = new_chunk;
		//@ divrem3((uintptr_t)chunk);
		//@ close mpool_chunk(new_chunk);
		//@ close mpool(p, _, _);
		//@ open_struct(chunk);
		
		//@ leak divrem((int)chunk, MPOOL_ENTRY_SIZE, _, 0);
		//@ leak divrem((int)new_chunk, MPOOL_ENTRY_SIZE, _, 0);
		//@ leak divrem((int)limit, MPOOL_ENTRY_SIZE, _, 0);
		//@ leak divrem((int)limit - (int)new_chunk, MPOOL_ENTRY_SIZE, _, 0);
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
	//@ requires p != NULL &*& [?f]mpool(p, ?non_empty, ?have_fb);
	//@ ensures [f]mpool(p, _, have_fb) &*& result != NULL ? chars(result, MPOOL_ENTRY_SIZE, _) : true;
{
	//@ struct mpool *old_p = p;
	
	// DIFF: hf uses a do-while loop here; when I use the annotations below with that loop vf fails to proove it, so I changed it to a while loop.
	while (p != NULL)
		//@ invariant [f]mpool(old_p, _, have_fb) &*& (p != old_p && p != NULL) ? [?ff]mpool(p, _, _) : true;
	{
		//@ leak p != old_p ? [_]mpool(p, _, _) : true;
		void *ret = mpool_alloc_no_fallback(p);

		if (ret != NULL) {
			return ret;
		}

		p = p->fallback;
	}

	return NULL;
}

/**
 * Frees an entry back into the memory pool, making it available for reuse.
 *
 * This is meant to be used for freeing single entries. To free multiple
 * entries, one must call mpool_add_chunk instead.
 */
void mpool_free(struct mpool *p, void *ptr)
	/*@
	requires 
		p != NULL
		&*& [?f]mpool(p, ?non_empty, ?have_fb)
		&*& ptr != 0
		&*& chars(ptr, MPOOL_ENTRY_SIZE, _)
		;
	@*/
	//@ ensures [f]mpool(p, true, have_fb);
{
	struct mpool_entry *e = ptr;
	//@ mpool_entry_raw_of_chars(ptr);

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
	// requires p != NULL &*& [?f]mpool(p, ?non_empty, ?have_fb) &*& align > 0 &*& count > 0;
	/*
	ensures 
		[f]mpool(p, _, have_fb)
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
	while (*prev != NULL)
		//@ invariant mpool(p, _, have_fb) &*& *prev |-> ?prev_chunk &*& prev_chunk != NULL ? mpool_chunk(prev_chunk) : true;
	{
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
