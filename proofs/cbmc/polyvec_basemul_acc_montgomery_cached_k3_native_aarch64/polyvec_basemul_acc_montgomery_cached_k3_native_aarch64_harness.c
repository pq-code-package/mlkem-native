// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>

#include "cbmc.h"
#include "common.h"

void mlk_polyvec_basemul_acc_montgomery_cached_k3_native(
    int16_t r[MLKEM_N], const int16_t a[3 * MLKEM_N],
    const int16_t b[3 * MLKEM_N], const int16_t b_cache[3 * (MLKEM_N / 2)]);

void harness(void)
{
  int16_t *r;
  const int16_t *a;
  const int16_t *b;
  const int16_t *b_cache;
  mlk_polyvec_basemul_acc_montgomery_cached_k3_native(r, a, b, b_cache);
}
