// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <kem.h>

void harness(void)
{
  uint8_t *a, *b, *c;
  mlk_kem_keypair_derand(a, b, c,
                         NULL /* context will be dropped by preprocessor */);
}
