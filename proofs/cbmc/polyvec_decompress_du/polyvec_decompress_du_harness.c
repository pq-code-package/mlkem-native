// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly.h"
#include "poly_k.h"

void harness(void)
{
  mlk_polyvec *a;
  uint8_t *r;

  mlk_polyvec_decompress_du(a, r);
}
