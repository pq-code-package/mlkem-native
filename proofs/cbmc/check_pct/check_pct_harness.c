// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "kem.h"

#define mlk_check_pct MLK_NAMESPACE_K(check_pct)
int mlk_check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                  uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES]);

void harness(void)
{
  uint8_t *a, *b;
  mlk_check_pct(a, b);
}
