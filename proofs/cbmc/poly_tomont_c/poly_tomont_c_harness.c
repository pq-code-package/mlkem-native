// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly.h"

// Prototype for the function under test
void mlk_poly_tomont_c(mlk_poly *r);

void harness(void)
{
  mlk_poly *a;

  mlk_poly_tomont_c(a);
}
