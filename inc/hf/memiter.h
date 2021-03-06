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
#ifdef HF_MEMITER_H
#else
#define HF_MEMITER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct memiter {
	const char *next;
	const char *limit;
};

void memiter_init(struct memiter *it, const void *data, size_t size);
bool memiter_parse_uint(struct memiter *it, uint64_t *value);
bool memiter_parse_str(struct memiter *it, struct memiter *str);
bool memiter_iseq(const struct memiter *it, const char *str);
bool memiter_advance(struct memiter *it, size_t v);

const void *memiter_base(const struct memiter *it);
size_t memiter_size(const struct memiter *it);

#endif
