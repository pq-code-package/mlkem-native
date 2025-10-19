// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "poly_k.h"

void mlk_polymat_permute_bitrev_to_custom(mlk_polymat a);

void harness(void)
{
  mlk_poly *a;
  mlk_polymat_permute_bitrev_to_custom(a);
}
