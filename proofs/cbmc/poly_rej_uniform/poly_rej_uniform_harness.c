// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "poly.h"

void harness(void)
{
  poly *out;
  uint8_t *seed;
  poly_rej_uniform(out, seed);
}
