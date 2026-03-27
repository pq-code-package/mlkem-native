// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <indcpa.h>

void harness(void)
{
  uint8_t *ct_u;
  mlk_polyvec *sp;
  mlk_poly *epp;
  mlk_polyvec_mulcache *sp_cache;
  uint8_t *seed;
  uint8_t *coins;
  mlk_indcpa_enc_u(ct_u, sp, epp, sp_cache, seed, coins,
                   NULL /* context will be dropped by preprocessor */);
}
