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

// #pragma once

#include "hf/boot_params.h"
#include "hf/manifest.h"
#include "hf/memiter.h"
#include "hf/mm.h"

bool boot_flow_init(const struct fdt_node *fdt_root, struct manifest *manifest,
		    struct boot_params *boot_params);

bool boot_flow_update(struct mm_stage1_locked stage1_locked,
		      const struct manifest *manifest,
		      struct boot_params_update *p, struct memiter *cpio,
		      struct mpool *ppool);
