// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly.h"

void harness(void)
{
  poly *r, *a, *b;
  poly_mulcache *b_cached;

  poly_basemul_montgomery_cached(r, a, b, b_cached);
}
