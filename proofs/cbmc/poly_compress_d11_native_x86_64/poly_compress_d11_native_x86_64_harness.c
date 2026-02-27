// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "compress.h"

int mlk_poly_compress_d11_native(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11],
                                 const int16_t a[MLKEM_N]);

void harness(void)
{
  /* mlk_poly_compress_d11 is only defined for MLKEM_K == 4 */
#if MLKEM_K == 4
  uint8_t *r;
  int16_t *a;
  int t;
  t = mlk_poly_compress_d11_native(r, a);
#endif /* MLKEM_K == 4 */
}
