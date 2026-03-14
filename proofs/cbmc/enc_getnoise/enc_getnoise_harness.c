// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

#define mlk_enc_getnoise MLK_NAMESPACE(enc_getnoise)
void mlk_enc_getnoise(mlk_polyvec *sp, mlk_polyvec *ep, mlk_poly *epp,
                      const uint8_t coins[MLKEM_SYMBYTES]);

void harness(void)
{
  mlk_polyvec *a, *b;
  mlk_poly *c;
  uint8_t *coins;

  {
    /* Dummy use of `free` to work around CBMC issue #8814. */
    free(NULL);
  }

  mlk_enc_getnoise(a, b, c, coins);
}
