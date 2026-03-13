// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

#define mlk_keypair_getnoise MLK_NAMESPACE(keypair_getnoise)
void mlk_keypair_getnoise(mlk_polyvec *pv, mlk_polyvec *e,
                          const uint8_t seed[MLKEM_SYMBYTES]);

void harness(void)
{
  mlk_polyvec *a, *b;
  uint8_t *seed;

  {
    /* Dummy use of `free` to work around CBMC issue #8814. */
    free(NULL);
  }

  mlk_keypair_getnoise(a, b, seed);
}
