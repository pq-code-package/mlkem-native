// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "indcpa.h"

void harness(void)
{
  mlk_poly *a;
  uint8_t *seed;
  int transposed;
  mlk_gen_matrix(a, seed, transposed);
}
