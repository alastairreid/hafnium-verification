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

#include "hf/dlog.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"
#include "util.h"

/**
 * The VM gets its memory size on boot, and can access it all.
 */
TEST(boot, memory_size)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "boot_memory", mb.send);

	run_res = spci_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.func, SPCI_YIELD_32);
}

/**
 * Accessing memory outside the given range aborts the VM.
 */
TEST(boot, beyond_memory_size)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "boot_memory_overrun", mb.send);

	run_res = spci_run(SERVICE_VM0, 0);
	EXPECT_SPCI_ERROR(run_res, SPCI_ABORTED);
}

/**
 * Accessing memory before the start of the image aborts the VM.
 */
TEST(boot, memory_before_image)
{
	struct spci_value run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	SERVICE_SELECT(SERVICE_VM0, "boot_memory_underrun", mb.send);

	run_res = spci_run(SERVICE_VM0, 0);
	EXPECT_SPCI_ERROR(run_res, SPCI_ABORTED);
}
