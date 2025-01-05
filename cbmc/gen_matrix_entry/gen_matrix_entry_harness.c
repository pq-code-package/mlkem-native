// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "poly.h"

// declare here since it's static in non-CBMC builds
#define gen_matrix_entry MLKEM_NAMESPACE(gen_matrix_entry)
void gen_matrix_entry(poly *entry, uint8_t seed[MLKEM_SYMBYTES + 16]);

void harness(void)
{
  poly *out;
  uint8_t *seed;
  gen_matrix_entry(out, seed);
}
