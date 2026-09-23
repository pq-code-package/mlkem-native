/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "example_context.h"

#include <stdio.h>
#include <stdlib.h>

static size_t example_align_up(size_t n)
{
  return (n + (EXAMPLE_ALLOC_ALIGN - 1)) & ~(size_t)(EXAMPLE_ALLOC_ALIGN - 1);
}

void example_context_init(example_context *context, uint8_t *buffer,
                          size_t buffer_size)
{
  if (buffer_size % EXAMPLE_ALLOC_ALIGN != 0)
  {
    fprintf(stderr, "ERROR: buffer size %u is not a multiple of %d\n",
            (unsigned)buffer_size, EXAMPLE_ALLOC_ALIGN);
    exit(1);
  }

  context->buffer = buffer;
  context->size = buffer_size;
  context->used = 0;
}

void *example_context_malloc(example_context *context, size_t size)
{
  size_t need;
  uint8_t *ptr;

  /* Reject allocations that cannot even be accommodated by an empty
   * allocator. Since `context->size` is aligned, this rules out overflow in
   * the alignment below. */
  if (size > context->size)
  {
    return NULL;
  }

  /* Round the request up so that every block stays aligned. */
  need = example_align_up(size);

  /* `used <= size` is an invariant, so the subtraction cannot underflow.
   * Exhaustion is not an error here: returning NULL makes mlkem-native unwind
   * and report MLK_ERR_OUT_OF_MEMORY. */
  if (need > context->size - context->used)
  {
    return NULL;
  }

  ptr = context->buffer + context->used;
  context->used += need;
  return ptr;
}

void example_context_free(example_context *context, void *ptr, size_t size)
{
  if (ptr == NULL)
  {
    return;
  }

  /* mlkem-native frees in LIFO order, so the to-be-freed region must be a
   * tail of the used memory region. To free it, we merely move the pointer. */
  if ((uint8_t *)ptr + example_align_up(size) !=
      context->buffer + context->used)
  {
    fprintf(stderr, "ERROR: free is not the most recent allocation\n");
    exit(1);
  }

  context->used -= example_align_up(size);
}
