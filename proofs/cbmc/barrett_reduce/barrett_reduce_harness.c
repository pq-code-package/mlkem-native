// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "common.h"

#define barrett_reduce MLK_NAMESPACE(barrett_reduce)
int16_t barrett_reduce(int16_t a);

void harness(void)
{
  int16_t a;
  int16_t r;

  r = barrett_reduce(a);
}
