// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly_k.h>

void harness(void)
{
  /* poly_getnoise_eta2() is only defined for MLKEM_K == 2, 4 */
#if MLKEM_K == 2 || MLKEM_K == 4
  uint8_t *seed;
  poly *r;
  uint8_t nonce;

  poly_getnoise_eta2(r, seed, nonce);
#endif /* MLKEM_K == 2 || MLKEM_K == 4 */
}
