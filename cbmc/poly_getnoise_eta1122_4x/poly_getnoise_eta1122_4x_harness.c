// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

void harness(void)
{
  /* poly_getnoise_eta1122_4x is only defines for MLKEM_K == 2 */
#if MLKEM_K == 2
  uint8_t *seed;
  poly *r0, *r1, *r2, *r3;
  uint8_t nonce0, nonce1, nonce2, nonce3;

  poly_getnoise_eta1122_4x(r0, r1, r2, r3, seed, nonce0, nonce1, nonce2,
                           nonce3);
#endif /* MLKEM_K == 2 */
}
