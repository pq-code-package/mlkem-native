// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <kem.h>

void harness(void)
{
  uint8_t *a, *b, *c;
  mlk_public_key *pk;
  crypto_kem_enc_derand_struct(a, b, pk, c);
}
