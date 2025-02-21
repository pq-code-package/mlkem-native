// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include "common.h"

#define mlk_scalar_signed_to_unsigned_q \
  MLK_NAMESPACE(scalar_signed_to_unsigned_q)
uint16_t mlk_scalar_signed_to_unsigned_q(int16_t c);

void harness(void)
{
  int16_t u;

  /* Contracts for this function are in poly.h */
  uint16_t d = mlk_scalar_signed_to_unsigned_q(u);
}
