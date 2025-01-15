// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>

void harness(void)
{
  uint64_t *state;
  unsigned char *data;
  unsigned int offset;
  unsigned int length;
  KeccakF1600_StateExtractBytes(state, data, offset, length);
}
