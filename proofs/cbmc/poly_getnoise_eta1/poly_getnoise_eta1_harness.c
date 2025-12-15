// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly_k.h>

void harness(void)
{
  uint8_t *seed;
  mlk_poly *r0;
  uint8_t nonce0;

  mlk_poly_getnoise_eta1(r0, seed, nonce0);
}
