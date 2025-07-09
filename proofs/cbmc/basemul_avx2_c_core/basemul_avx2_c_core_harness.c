// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "common.h"

#include "poly.h"

int16_t fqmul(int16_t a, int16_t b)
{
  return mlk_montgomery_reduce((int32_t)a * (int32_t)b);
}

void basemul_avx2_c_core(int16_t r[2], int16_t a[2], int16_t b[2], int16_t bc)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * 2))
  requires(memory_no_alias(a, sizeof(int16_t) * 2))
  requires(memory_no_alias(b, sizeof(int16_t) * 2))
  requires(array_abs_bound(a, 0, 2, MLKEM_UINT12_LIMIT))
  assigns(object_whole(r))
  ensures(array_abs_bound(r, 0, 2, INT16_MAX / 4)))
{
  r[0] = fqmul(a[0], b[0]) + fqmul(a[1], bc);
  r[1] = fqmul(a[0], b[1]) + fqmul(a[1], b[0]);
}

void harness(void)
{
  int16_t *r, *a, *b;
  int16_t bc;
  basemul_avx2_c_core(r, a, b, bc);
}
