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

/** AArch64-specific API */

/**
 * Ensures explicit memory accesses before this point are completed before any
 * later memory accesses are performed. The instruction argument specifies:
 *   - the shareability domain over which the instruction must operate,
 *   - the accesses for which the instruction operates.
 */
#if 1
#define dmb(arg) do {} while(0)
#else
#define dmb(arg)                               \
	do {                                   \
		__asm__ volatile("dmb " #arg); \
	} while (0)
#endif

/**
 * Ensures explicit memory access and management instructions have completed
 * before continuing. The instruction argument specifies:
 *   - the shareability domain over which the instruction must operate,
 *   - the accesses for which the instruction operates.
 */
#if 1
#define dsb(arg) do {} while(0)
#else
#define dsb(arg)                               \
	do {                                   \
		__asm__ volatile("dsb " #arg); \
	} while (0)
#endif

/**
 * Flushes the instruction pipeline so that instructions are fetched from
 * memory.
 */
#if 1
#define isb(arg) do {} while(0)
#else
#define isb()                            \
	do {                             \
		__asm__ volatile("isb"); \
	} while (0)
#endif

/** Platform-agnostic API */

/**
 * Ensures all explicit memory accesses before this point are completed before
 * any later memory accesses are performed.
 */
#define memory_ordering_barrier() dmb(sy)

/**
 * Ensures all explicit memory access and management instructions have completed
 * before continuing.
 */
#define data_sync_barrier() dsb(sy)
