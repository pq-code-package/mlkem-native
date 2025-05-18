// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

void mlk_poly_mulcache_compute_native(int16_t cache[MLKEM_N / 2],
                                      const int16_t mlk_poly[MLKEM_N]);

void harness(void)
{
  int16_t *r, *c;
  mlk_poly_mulcache_compute_native(c, r);
}
