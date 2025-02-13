// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "kem.h"

#define check_pct MLK_NAMESPACE_K(check_pct)
int check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
              uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES]);

void harness(void)
{
  uint8_t *a, *b;
  check_pct(a, b);
}
