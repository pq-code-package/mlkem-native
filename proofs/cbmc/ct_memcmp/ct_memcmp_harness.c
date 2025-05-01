// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "verify.h"

void harness(void)
{
  uint8_t *a;
  uint8_t *b;
  size_t len;
  int r;
  r = mlk_ct_memcmp(a, b, len);
}
