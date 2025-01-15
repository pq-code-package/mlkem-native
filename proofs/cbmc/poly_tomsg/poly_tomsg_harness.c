// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

void harness(void)
{
  poly *a;
  uint8_t *msg;

  /* Contracts for this function are in poly.h */
  poly_tomsg(msg, a);
}
