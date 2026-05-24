// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <kem.h>

void harness(void)
{
  uint8_t *ct_v, *sp_serial, *epp_serial;
  uint8_t *coins, *ek_vector;
  mlk_kem_enc_v(ct_v, sp_serial, epp_serial, coins, ek_vector,
                NULL /* context will be dropped by preprocessor */);
}
