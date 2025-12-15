// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

int mlk_poly_frombytes_native(int16_t r[MLKEM_N],
                              const uint8_t a[MLKEM_POLYBYTES]);

void harness(void)
{
  uint16_t *r;
  uint8_t *a;
  int t;
  t = mlk_poly_frombytes_native(r, a);
}
