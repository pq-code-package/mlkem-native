// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include "common.h"

#define scalar_signed_to_unsigned_q MLKEM_NAMESPACE(scalar_signed_to_unsigned_q)
uint16_t scalar_signed_to_unsigned_q(int16_t c);

void harness(void)
{
  int16_t u;

  /* Contracts for this function are in poly.h */
  uint16_t d = scalar_signed_to_unsigned_q(u);
}
