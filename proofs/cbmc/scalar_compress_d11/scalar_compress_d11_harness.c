// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

void harness(void)
{
  int16_t u;

  /* Contracts for this function are in compress.h */
  uint16_t d = mlk_scalar_compress_d11(u);
}
