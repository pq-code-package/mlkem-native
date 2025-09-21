// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "compress.h"

void harness(void)
{
  mlk_poly *a;
  uint8_t *r;

  mlk_poly_compress_d5_c(r, a);
}
