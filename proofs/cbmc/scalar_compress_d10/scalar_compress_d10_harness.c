// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

void harness(void)
{
  uint16_t u;

  /* Contracts for this function are in compress.h */
  uint32_t d = mlk_scalar_compress_d10(u);
}
