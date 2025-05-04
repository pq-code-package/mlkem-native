// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <kem.h>

void harness(void)
{
  uint8_t *a;
  mlk_secret_key *sk;
  mlk_public_key *pk;
  crypto_kem_keypair_derand_struct(pk, sk, a);
}
