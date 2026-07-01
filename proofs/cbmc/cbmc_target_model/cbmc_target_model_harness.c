// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <stddef.h>
#include <stdint.h>

void __CPROVER_assert(_Bool, const char *);

void harness(void)
{
  __CPROVER_assert(sizeof(void *) == CBMC_TARGET_POINTER_BYTES,
                   "CBMC target pointer width matches selected model");
  __CPROVER_assert(sizeof(size_t) == CBMC_TARGET_SIZE_T_BYTES,
                   "CBMC target size_t width matches selected model");
  __CPROVER_assert(sizeof(long) == CBMC_TARGET_LONG_BYTES,
                   "CBMC target long width matches selected model");
  __CPROVER_assert(sizeof(uint64_t) == 8,
                   "CBMC target uint64_t width is 8 bytes");
}
