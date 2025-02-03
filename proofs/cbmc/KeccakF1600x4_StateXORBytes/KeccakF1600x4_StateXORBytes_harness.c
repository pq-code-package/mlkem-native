// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>

void harness(void)
{
  uint64_t *state;
  const unsigned char *data0, *data1, *data2, *data3;
  unsigned offset;
  unsigned length;
  KeccakF1600x4_StateXORBytes(state, data0, data1, data2, data3, offset,
                              length);
}
