// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

int mlk_poly_decompress_d11_native(
    int16_t r[MLKEM_N], const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D11]);

void harness(void)
{
  /* mlk_poly_decompress_d11 is only defined for MLKEM_K == 4 */
#if MLKEM_K == 4
  int16_t *r;
  uint8_t *a;
  int t;
  t = mlk_poly_decompress_d11_native(r, a);
#endif /* MLKEM_K == 4 */
}
