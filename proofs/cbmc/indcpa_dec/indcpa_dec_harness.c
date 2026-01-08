// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

void harness(void)
{
  uint8_t *m, *c, *sk;
  mlk_indcpa_dec(m, c, sk, NULL /* context will be dropped by preprocessor */);
}
