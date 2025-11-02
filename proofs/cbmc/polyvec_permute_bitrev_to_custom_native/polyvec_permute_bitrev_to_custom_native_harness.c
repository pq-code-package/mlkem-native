// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "poly_k.h"

void mlk_polyvec_permute_bitrev_to_custom(mlk_polyvec *v);

void harness(void)
{
  mlk_polyvec *v;
  mlk_polyvec_permute_bitrev_to_custom(v);
}
