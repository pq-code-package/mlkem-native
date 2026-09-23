/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef EXAMPLE_CONTEXT_H
#define EXAMPLE_CONTEXT_H

#include <stddef.h>
#include <stdint.h>

/* Alignment used for every allocation. 32 bytes is the strictest requirement
 * of any type mlkem-native allocates -- the AVX2 backend needs it for its
 * aligned loads, other backends need less -- and we are conservative and apply
 * it throughout. mlkem-native's own MLK_DEFAULT_ALIGN carries the same value,
 * but is internal to the library, so we restate it here. */
#define EXAMPLE_ALLOC_ALIGN 32

/* This mirrors MLK_ALIGN from mlkem/src/sys.h, including the fallback to no
 * alignment at all: on a toolchain that cannot express the constraint, the
 * library's own buffers are equally unaligned, so we are no worse off. */
#if defined(__GNUC__)
#define EXAMPLE_ALIGN __attribute__((aligned(EXAMPLE_ALLOC_ALIGN)))
#elif defined(_MSC_VER)
#define EXAMPLE_ALIGN __declspec(align(EXAMPLE_ALLOC_ALIGN))
#else
#define EXAMPLE_ALIGN /* No known support for alignment constraints */
#endif

/*
 * Application context threaded through the mlkem-native API.
 *
 * Here it holds a bump allocator: `buffer` is the base of the region, and
 * `used` is the cursor bounding the part currently handed out. Since
 * mlkem-native deallocates in reverse order of allocation, freeing is just a
 * matter of moving the cursor back; no per-allocation bookkeeping is needed.
 */
typedef struct
{
  uint8_t *buffer;
  size_t size;
  size_t used;
} example_context;

/* `buffer` must be declared with EXAMPLE_ALIGN, and `buffer_size` must be a
 * multiple of EXAMPLE_ALLOC_ALIGN. */
void example_context_init(example_context *context, uint8_t *buffer,
                          size_t buffer_size);

void *example_context_malloc(example_context *context, size_t size);
void example_context_free(example_context *context, void *ptr, size_t size);

#endif /* !EXAMPLE_CONTEXT_H */
