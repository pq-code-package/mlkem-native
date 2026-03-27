// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <indcpa.h>

void harness(void)
{
  uint8_t *ct_v;
  mlk_polyvec *sp;
  mlk_poly *epp;
  mlk_polyvec_mulcache *sp_cache;
  uint8_t *m;
  uint8_t *ek_vector;
  mlk_indcpa_enc_v(ct_v, sp, epp, sp_cache, m, ek_vector,
                   NULL /* context will be dropped by preprocessor */);
}
