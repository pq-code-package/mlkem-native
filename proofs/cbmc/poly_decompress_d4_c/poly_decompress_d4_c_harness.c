// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "compress.h"

void harness(void)
{
  mlk_poly *r;
  uint8_t *a;

  mlk_poly_decompress_d4_c(r, a);
}
