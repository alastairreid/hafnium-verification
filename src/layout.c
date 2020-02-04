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

#include "hf/layout.h"

#include "hf/std.h"

extern uint8_t text_begin[];
extern uint8_t text_end[];
extern uint8_t rodata_begin[];
extern uint8_t rodata_end[];
extern uint8_t data_begin[];
extern uint8_t data_end[];
extern uint8_t initrd_begin[];
extern uint8_t initrd_end[];
extern uint8_t fdt_begin[];
extern uint8_t fdt_end[];
extern uint8_t image_end[];

/**
 * Get the address the .text section begins at.
 */
paddr_t layout_text_begin(void)
{
	return pa_init((uintpaddr_t)text_begin);
}

/**
 * Get the address the .text section ends at.
 */
paddr_t layout_text_end(void)
{
	return pa_init((uintpaddr_t)text_end);
}

/**
 * Get the address the .rodata section begins at.
 */
paddr_t layout_rodata_begin(void)
{
	return pa_init((uintpaddr_t)rodata_begin);
}

/**
 * Get the address the .rodata section ends at.
 */
paddr_t layout_rodata_end(void)
{
	return pa_init((uintpaddr_t)rodata_end);
}

/**
 * Get the address the .data section begins at.
 */
paddr_t layout_data_begin(void)
{
	return pa_init((uintpaddr_t)data_begin);
}

/**
 * Get the address the .data section ends at.
 */
paddr_t layout_data_end(void)
{
	return pa_init((uintpaddr_t)data_end);
}

/**
 * Get the address the .initrd section begins at.
 */
paddr_t layout_initrd_begin(void)
{
	return pa_init((uintpaddr_t)initrd_begin);
}

/**
 * Get the address the .initrd section ends at.
 */
paddr_t layout_initrd_end(void)
{
	return pa_init((uintpaddr_t)initrd_end);
}

/**
 * Get the address the .fdt section begins at.
 */
paddr_t layout_fdt_begin(void)
{
	return pa_init((uintpaddr_t)fdt_begin);
}

/**
 * Get the address the .fdt section ends at.
 */
paddr_t layout_fdt_end(void)
{
	return pa_init((uintpaddr_t)fdt_end);
}

/**
 * Get the address the loaded image ends at.
 */
paddr_t layout_image_end(void)
{
	return pa_init((uintpaddr_t)image_end);
}

/**
 * Get the address to load the primary VM at.
 *
 * This is placed just after the image.
 */
paddr_t layout_primary_begin(void)
{
	paddr_t image_end = layout_image_end();

	/*
	 * Linux usually expects to be loaded at offset 0x80000 into a 2MB
	 * aligned address.
	 * TODO: This is a hack, and isn't always correct. We should really read
	 * the alignment from the header of the binary, or have a bootloader
	 * within the VM do so.
	 */
	return pa_init(align_up(pa_addr(image_end), 0x200000) + 0x80000);
}
