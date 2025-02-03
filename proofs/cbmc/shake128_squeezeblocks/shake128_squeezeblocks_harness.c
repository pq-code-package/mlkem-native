// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <fips202.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

void harness(void)
{
  uint8_t *output;
  size_t nblocks;
  shake128ctx *state;
  shake128_squeezeblocks(output, nblocks, state);
}
