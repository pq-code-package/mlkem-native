// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

int mlk_poly_tobytes_native(uint8_t r[MLKEM_POLYBYTES],
                            const int16_t a[MLKEM_N]);

void harness(void)
{
  uint8_t *r;
  int16_t *a;
  int t;
  t = mlk_poly_tobytes_native(r, a);
}
