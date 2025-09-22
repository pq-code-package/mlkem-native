// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

// Prototype for the function under test
void mlk_poly_tobytes_c(uint8_t r[MLKEM_POLYBYTES], const mlk_poly *a);

void harness(void)
{
  mlk_poly *a;
  uint8_t *r;

  /* Contracts for this function are in compress.h */
  mlk_poly_tobytes_c(r, a);
}
