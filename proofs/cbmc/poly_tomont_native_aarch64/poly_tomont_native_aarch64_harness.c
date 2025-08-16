// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

int mlk_poly_tomont_native(int16_t p[MLKEM_N]);

void harness(void)
{
  int16_t *r;
  int t;
  t = mlk_poly_tomont_native(r);
}
