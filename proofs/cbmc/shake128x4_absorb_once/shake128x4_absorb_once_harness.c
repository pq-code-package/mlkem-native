// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <fips202x4.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

void harness(void)
{
  mlk_shake128x4ctx *state;
  const uint8_t *in0, in1, in2, in3;
  size_t inlen;
  mlk_shake128x4_absorb_once(state, in0, in1, in2, in3, inlen);
}
