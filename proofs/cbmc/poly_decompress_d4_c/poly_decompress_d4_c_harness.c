// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

void mlk_poly_decompress_d4_c(mlk_poly *r,
                              const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D4]);

void harness(void)
{
#if MLKEM_K != 4
  mlk_poly *r;
  uint8_t *a;
  mlk_poly_decompress_d4_c(r, a);
#endif
}
