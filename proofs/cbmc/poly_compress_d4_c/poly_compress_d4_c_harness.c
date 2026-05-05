// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

void mlk_poly_compress_d4_c(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4],
                            const mlk_poly *a);

void harness(void)
{
#if MLKEM_K != 4
  uint8_t *r;
  mlk_poly *a;
  mlk_poly_compress_d4_c(r, a);
#endif
}
