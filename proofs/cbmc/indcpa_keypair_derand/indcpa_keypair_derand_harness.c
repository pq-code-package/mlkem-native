// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

void harness(void)
{
  uint8_t *c;
  mlk_indcpa_public_key *a;
  mlk_indcpa_secret_key *b;
  mlk_indcpa_keypair_derand(a, b, c);
}
