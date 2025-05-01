// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

void harness(void)
{
  mlk_poly *a;

  /* Contracts for this function are in compress.h */
  mlk_poly_reduce(a);
}
