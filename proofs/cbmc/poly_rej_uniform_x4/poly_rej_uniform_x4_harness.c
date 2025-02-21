// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "sampling.h"

void harness(void)
{
  mlk_poly out[4];
  uint8_t *seed[4];
  mlk_poly_rej_uniform_x4(out, seed);
}
