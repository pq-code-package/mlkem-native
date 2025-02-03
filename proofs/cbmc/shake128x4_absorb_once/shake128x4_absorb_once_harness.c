// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <fips202x4.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

void harness(void)
{
  shake128x4ctx *state;
  const uint8_t *in0, in1, in2, in3;
  size_t inlen;
  shake128x4_absorb_once(state, in0, in1, in2, in3, inlen);
}
