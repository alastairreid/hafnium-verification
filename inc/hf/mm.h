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
#ifdef HF_MM_H
#else
#define HF_MM_H

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>

#include "hf/arch/mm.h"

#include "hf/addr.h"
#include "hf/mpool.h"
#include "hf/static_assert.h"

/* Keep macro alignment */
/* clang-format off */

#define PAGE_SIZE (1 << PAGE_BITS)
//#define MM_PTE_PER_PAGE (PAGE_SIZE / sizeof(pte_t))
#define MM_PTE_PER_PAGE 512

/* The following are arch-independent page mapping modes. */
#define MM_MODE_R UINT32_C(0x0001) /* read */
#define MM_MODE_W UINT32_C(0x0002) /* write */
#define MM_MODE_X UINT32_C(0x0004) /* execute */
#define MM_MODE_D UINT32_C(0x0008) /* device */

/*
 * Memory in stage-1 is either valid (present) or invalid (absent).
 *
 * Memory in stage-2 has more states to track sharing, borrowing and giving of
 * memory. The states are made up of three parts:
 *
 *  1. V = valid/invalid    : Whether the memory is part of the VM's address
 *                            space. A fault will be generated if accessed when
 *                            invalid.
 *  2. O = owned/unowned    : Whether the memory is owned by the VM.
 *  3. X = exclusive/shared : Whether access is exclusive to the VM or shared
 *                            with at most one other.
 *
 * These parts compose to form the following state:
 *
 *  -  V  O  X : Owner of memory with exclusive access.
 *  -  V  O !X : Owner of memory with access shared with at most one other VM.
 *  -  V !O  X : Borrower of memory with exclusive access.
 *  -  V !O !X : Borrower of memory where access is shared with the owner.
 *  - !V  O  X : Owner of memory lent to a VM that has exclusive access.
 *
 *  - !V  O !X : Unused. Owner of shared memory always has access.
 *  - !V !O  X : Unused. Next entry is used for invalid memory.
 *
 *  - !V !O !X : Invalid memory. Memory is unrelated to the VM.
 *
 *  Modes are selected so that owner of exclusive memory is the default.
 */
#define MM_MODE_INVALID UINT32_C(0x0010)
#define MM_MODE_UNOWNED UINT32_C(0x0020)
#define MM_MODE_SHARED  UINT32_C(0x0040)

/* The mask for a mode that is considered unmapped. */
#define MM_MODE_UNMAPPED_MASK (MM_MODE_INVALID | MM_MODE_UNOWNED)

#define MM_FLAG_COMMIT  0x01
#define MM_FLAG_UNMAP   0x02
#define MM_FLAG_STAGE1  0x04

/* clang-format on */

struct mm_page_table {
	alignas(PAGE_SIZE) pte_t entries[MM_PTE_PER_PAGE];
};
#if 0
static_assert(sizeof(struct mm_page_table) == PAGE_SIZE,
	      "A page table must take exactly one page.");
static_assert(alignof(struct mm_page_table) == PAGE_SIZE,
	      "A page table must be page aligned.");
#endif

struct mm_ptable {
	/** Address of the root of the page table. */
	paddr_t root;
};

/*@
predicate mm_ptable(struct mm_ptable *ptable) =
	true;
@*/

/** The type of addresses stored in the page table. */
typedef uintvaddr_t ptable_addr_t;

/** Represents the currently locked stage-1 page table of the hypervisor. */
struct mm_stage1_locked {
	struct mm_ptable *ptable;
};

/*@
predicate mm_stage1_locked(struct mm_stage1_locked *stage) =
	mm_ptable(stage->ptable);
@*/

void mm_vm_enable_invalidation(void);

bool mm_ptable_init(struct mm_ptable *t, int flags, struct mpool *ppool);
ptable_addr_t mm_ptable_addr_space_end(int flags);

bool mm_vm_init(struct mm_ptable *t, struct mpool *ppool);
void mm_vm_fini(struct mm_ptable *t, struct mpool *ppool);
bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
			uint32_t mode, struct mpool *ppool, ipaddr_t *ipa);
bool mm_vm_identity_prepare(struct mm_ptable *t, paddr_t begin, paddr_t end,
			    uint32_t mode, struct mpool *ppool);
void mm_vm_identity_commit(struct mm_ptable *t, paddr_t begin, paddr_t end,
			   uint32_t mode, struct mpool *ppool, ipaddr_t *ipa);
bool mm_vm_unmap(struct mm_ptable *t, paddr_t begin, paddr_t end,
		 struct mpool *ppool);
void mm_vm_defrag(struct mm_ptable *t, struct mpool *ppool);
void mm_vm_dump(struct mm_ptable *t);
bool mm_vm_get_mode(struct mm_ptable *t, ipaddr_t begin, ipaddr_t end,
		    uint32_t *mode);

struct mm_stage1_locked *mm_lock_stage1(void);
	//@ requires true;
	//@ ensures mm_ptable(result);

void mm_unlock_stage1(struct mm_stage1_locked *lock);
	//@ requires mm_ptable(lock->ptable);
	//@ ensures true;

void *mm_identity_map(struct mm_stage1_locked stage1_locked, paddr_t begin,
		      paddr_t end, uint32_t mode, struct mpool *ppool);
	//@ requires true;
	//@ ensures true;

bool mm_unmap(struct mm_stage1_locked stage1_locked, paddr_t begin, paddr_t end,
	      struct mpool *ppool);
	//@ requires true;
	//@ ensures true;

void mm_defrag(struct mm_stage1_locked stage1_locked, struct mpool *ppool);
	//@ requires true;
	//@ ensures true;

bool mm_init(struct mpool *ppool);
	//@ requires mpool(ppool);
	//@ ensures mpool(ppool);

#endif
