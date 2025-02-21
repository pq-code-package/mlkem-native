// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>
#include <poly.h>

void harness(void)
{
  uint8_t *a, *b, *c, *d;
  mlk_indcpa_enc(a, b, c, d);
}
