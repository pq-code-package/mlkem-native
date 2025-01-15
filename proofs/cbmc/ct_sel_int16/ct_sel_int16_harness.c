// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "verify.h"

void harness(void)
{
  int16_t a, b, c;
  uint16_t cond;

  c = ct_sel_int16(a, b, cond);
}
