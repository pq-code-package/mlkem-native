// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include <stdint.h>
#include "common.h"


int16_t mlk_fqmul(int16_t a, int16_t b);

void harness(void)
{
  int16_t a, b, r;

  r = mlk_fqmul(a, b);
}
