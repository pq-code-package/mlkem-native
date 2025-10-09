// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "indcpa.h"
#include "poly_k.h"

#define mlk_matvec_mul MLK_ADD_PARAM_SET(mlk_matvec_mul)
void mlk_matvec_mul(mlk_polyvec out, const mlk_polymat a, const mlk_polyvec v,
                    const mlk_polyvec_mulcache vc);

void harness(void)
{
  mlk_poly *out;
  mlk_poly *a;
  mlk_poly *v;
  mlk_poly_mulcache *vc;
  mlk_matvec_mul(out, a, v, vc);
}
