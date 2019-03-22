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

#include "hf/arch/std.h"
#include "hf/arch/vm/registers.h"

#include "hf/spci.h"

#include "vmapi/hf/call.h"

#include "hftest.h"
#include "primary_with_secondary.h"
#include "util.h"

/**
 * Test that floating point registers are saved and restored by
 * filling them with one value here and a different value in the
 * service.
 */
TEST(floating_point, fp_fill)
{
	const double first = 1.2;
	const double second = -2.3;
	struct hf_vcpu_run_return run_res;
	struct mailbox_buffers mb = set_up_mailbox();

	fill_fp_registers(first);
	SERVICE_SELECT(SERVICE_VM0, "fp_fill", mb.send);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
	EXPECT_EQ(check_fp_register(first), true);

	fill_fp_registers(second);
	run_res = hf_vcpu_run(SERVICE_VM0, 0);
	EXPECT_EQ(run_res.code, HF_VCPU_RUN_YIELD);
	EXPECT_EQ(check_fp_register(second), true);
}
