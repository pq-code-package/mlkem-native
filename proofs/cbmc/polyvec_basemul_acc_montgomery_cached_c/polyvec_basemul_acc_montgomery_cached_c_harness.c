// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly_k.h"

#define mlk_polyvec_basemul_acc_montgomery_cached_c \
  MLK_ADD_PARAM_SET(mlk_polyvec_basemul_acc_montgomery_cached_c)
void mlk_polyvec_basemul_acc_montgomery_cached_c(
    mlk_poly *r, const mlk_polyvec a, const mlk_polyvec b,
    const mlk_polyvec_mulcache b_cache);

void harness(void)
{
  mlk_poly *r, *a, *b;
  mlk_poly_mulcache *b_cache;

  mlk_polyvec_basemul_acc_montgomery_cached_c(r, a, b, b_cache);
}
