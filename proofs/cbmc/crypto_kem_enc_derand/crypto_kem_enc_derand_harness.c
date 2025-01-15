// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <kem.h>

void harness(void)
{
  uint8_t *a, *b, *c, *d;
  crypto_kem_enc_derand(a, b, c, d);
}
