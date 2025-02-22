// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "indcpa.h"
#include "poly_k.h"

#define mlk_matvec_mul MLK_NAMESPACE(matvec_mul)
void mlk_matvec_mul(mlk_polyvec *out, mlk_polyvec const *a,
                    mlk_polyvec const *v, mlk_polyvec_mulcache const *vc);

void harness(void)
{
  mlk_polyvec *out, *a, *v;
  mlk_polyvec_mulcache *vc;
  mlk_matvec_mul(out, a, v, vc);
}
