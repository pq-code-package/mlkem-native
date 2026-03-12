// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <kem.h>

void harness(void)
{
  uint8_t *ct_u, *ss, *sp_serial, *epp_serial;
  uint8_t *seed, *hpk, *coins;
  mlk_kem_enc_derand_u(ct_u, ss, sp_serial, epp_serial, seed, hpk, coins,
                        NULL /* context will be dropped by preprocessor */);
}
