// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "params.h"

void mlk_poly_permute_bitrev_to_custom(int16_t data[MLKEM_N]);

void harness(void)
{
  int16_t data[MLKEM_N];
  mlk_poly_permute_bitrev_to_custom(data);
}
