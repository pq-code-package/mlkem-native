// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly.h"

void mlk_poly_mulcache_compute_c(mlk_poly_mulcache *x, const mlk_poly *a);

void harness(void)
{
  mlk_poly_mulcache *x;
  mlk_poly *a;

  mlk_poly_mulcache_compute_c(x, a);
}
