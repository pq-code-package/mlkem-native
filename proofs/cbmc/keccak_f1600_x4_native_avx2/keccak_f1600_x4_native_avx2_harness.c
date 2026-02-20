// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>

int mlk_keccak_f1600_x4_native(uint64_t *state);

void harness(void)
{
  uint64_t *s;
  int t = mlk_keccak_f1600_x4_native(s);
}
