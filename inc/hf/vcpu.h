/*
 * Copyright 2019 The Hafnium Authors.
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
#ifdef HF_VCPU_H
#else
#define HF_VCPU_H

#include "hf/addr.h"
#include "hf/spinlock.h"

#include "vmapi/hf/spci.h"
struct cpu;
struct vm;

/** The number of bits in each element of the interrupt bitfields. */
#define INTERRUPT_REGISTER_BITS 32

enum vcpu_state {
	/** The vCPU is switched off. */
	VCPU_STATE_OFF,

	/** The vCPU is ready to be run. */
	VCPU_STATE_READY,

	/** The vCPU is currently running. */
	VCPU_STATE_RUNNING,

	/** The vCPU is waiting for a message. */
	VCPU_STATE_BLOCKED_MAILBOX,

	/** The vCPU is waiting for an interrupt. */
	VCPU_STATE_BLOCKED_INTERRUPT,

	/** The vCPU has aborted. */
	VCPU_STATE_ABORTED
};

struct interrupts {
	/** Bitfield keeping track of which interrupts are enabled. */
	uint32_t interrupt_enabled[2];
	/** Bitfield keeping track of which interrupts are pending. */
	uint32_t interrupt_pending[2];
	/**
	 * The number of interrupts which are currently both enabled and
	 * pending. i.e. the number of bits set in interrupt_enable &
	 * interrupt_pending.
	 */
	uint32_t enabled_and_pending_count;
};

struct vcpu_fault_info {
	ipaddr_t ipaddr;
	vaddr_t vaddr;
	vaddr_t pc;
	uint32_t mode;
};

struct vcpu {
	struct spinlock lock;

	/*
	 * The state is only changed in the context of the vCPU being run. This
	 * ensures the scheduler can easily keep track of the vCPU state as
	 * transitions are indicated by the return code from the run call.
	 */
	enum vcpu_state state;

	struct cpu *cpu;
	struct vm *vm;
	struct arch_regs regs;
	struct interrupts interrupts;

	/*
	 * Determine whether the 'regs' field is available for use. This is set
	 * to false when a vCPU is about to run on a physical CPU, and is set
	 * back to true when it is descheduled.
	 */
	bool regs_available;
};

/** Encapsulates a vCPU whose lock is held. */
struct vcpu_locked {
	struct vcpu *vcpu;
};

struct vcpu_locked vcpu_lock(struct vcpu *vcpu);
void vcpu_unlock(struct vcpu_locked *locked);
void vcpu_init(struct vcpu *vcpu, struct vm *vm);
void vcpu_on(struct vcpu_locked vcpu, ipaddr_t entry, uintreg_t arg);
spci_vcpu_index_t vcpu_index(const struct vcpu *vcpu);
bool vcpu_is_off(struct vcpu_locked vcpu);
bool vcpu_secondary_reset_and_start(struct vcpu *vcpu, ipaddr_t entry,
				    uintreg_t arg);

bool vcpu_handle_page_fault(const struct vcpu *current,
			    struct vcpu_fault_info *f);
#endif
