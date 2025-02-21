// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly_k.h"

void harness(void)
{
  mlk_poly *r;
  mlk_polyvec *a, *b;
  mlk_polyvec_mulcache *b_cached;

  mlk_polyvec_basemul_acc_montgomery_cached(r, a, b, b_cached);
}
