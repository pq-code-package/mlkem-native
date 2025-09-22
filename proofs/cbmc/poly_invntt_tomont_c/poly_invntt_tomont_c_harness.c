// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly.h"

void mlk_poly_invntt_tomont_c(mlk_poly *p);

void harness(void)
{
  mlk_poly *p;
  mlk_poly_invntt_tomont_c(p);
}
