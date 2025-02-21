// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "verify.h"

void harness(void)
{
  uint8_t *x, *y;
  size_t len;
  uint8_t b;
  mlk_ct_cmov_zero(x, y, len, b);
}
