// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <fips202x4.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

void harness(void)
{
  uint8_t *output0, output1, output2, output3;
  size_t outlen;
  const uint8_t *input0, input1, input2, input3;
  size_t inlen;
  mlk_shake256x4(output0, output1, output2, output3, outlen, input0, input1,
                 input2, input3, inlen);
}
