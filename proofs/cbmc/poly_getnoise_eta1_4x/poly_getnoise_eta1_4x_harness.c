// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly_k.h>

void harness(void)
{
  uint8_t *seed;
  mlk_poly *r0, *r1, *r2, *r3;
  uint8_t nonce0, nonce1, nonce2, nonce3;

  mlk_poly_getnoise_eta1_4x(r0, r1, r2, r3, seed, nonce0, nonce1, nonce2,
                            nonce3);
}
