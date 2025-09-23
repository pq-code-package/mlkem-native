// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

// Prototype for the function under test
void mlk_poly_reduce_c(mlk_poly *r);

void harness(void)
{
  mlk_poly *a;

  /* Contracts for this function are in poly.h */
  mlk_poly_reduce_c(a);
}
