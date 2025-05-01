// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

void harness(void)
{
  mlk_poly *a;
  uint8_t *r;

  /* Contracts for this function are in compress.h */
  mlk_poly_tobytes(r, a);
}
