// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>

void harness(void)
{
  uint64_t *state;
  const unsigned char *data;
  unsigned offset;
  unsigned length;
  KeccakF1600_StateXORBytes(state, data, offset, length);
}
