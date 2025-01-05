// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "poly.h"

// declare here since it's static in non-CBMC builds
#define gen_matrix_entry_x4 MLKEM_NAMESPACE(gen_matrix_entry_x4)
void gen_matrix_entry_x4(poly vec[4], uint8_t *seed[4]);

void harness(void)
{
  poly out[4];
  uint8_t *seed[4];
  gen_matrix_entry_x4(out, seed);
}
