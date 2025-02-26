// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <kem.h>

void harness(void)
{
  uint8_t *pk;
  mlk_public_key *pks;
  crypto_kem_parse_pk(pks, pk);
}
