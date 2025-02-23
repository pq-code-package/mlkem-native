// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "common.h"

#define mlk_montgomery_reduce MLK_NAMESPACE(montgomery_reduce)
int16_t mlk_montgomery_reduce(int32_t a);

void harness(void)
{
  int32_t a;
  int16_t r;

  r = mlk_montgomery_reduce(a);
}
