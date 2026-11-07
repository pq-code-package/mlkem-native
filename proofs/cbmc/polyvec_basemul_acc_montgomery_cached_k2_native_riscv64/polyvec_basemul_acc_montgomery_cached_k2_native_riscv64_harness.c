// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>

#include "cbmc.h"
#include "common.h"

int mlk_polyvec_basemul_acc_montgomery_cached_k2_native(
    int16_t r[MLKEM_N], const int16_t a[2 * MLKEM_N],
    const int16_t b[2 * MLKEM_N], const int16_t b_cache[2 * (MLKEM_N / 2)]);

void harness(void)
{
  int16_t *r;
  const int16_t *a;
  const int16_t *b;
  const int16_t *b_cache;
  int t;
  t = mlk_polyvec_basemul_acc_montgomery_cached_k2_native(r, a, b, b_cache);
}
