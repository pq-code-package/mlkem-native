// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "sampling.h"

void harness(void)
{
  mlk_poly *out;
  uint8_t *seed;
  mlk_poly_rej_uniform(out, seed);
}
