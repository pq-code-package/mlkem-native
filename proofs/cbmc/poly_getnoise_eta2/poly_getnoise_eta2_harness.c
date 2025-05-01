// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly_k.h>

void harness(void)
{
  /* mlk_poly_getnoise_eta2() is only defined for MLKEM_K == 2, 4 */
#if MLKEM_K == 2 || MLKEM_K == 4
  uint8_t *seed;
  mlk_poly *r;
  uint8_t nonce;

  mlk_poly_getnoise_eta2(r, seed, nonce);
#endif /* MLKEM_K == 2 || MLKEM_K == 4 */
}
