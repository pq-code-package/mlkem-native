/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Custom FIPS202-x4 header for test/src/test_fips202_fail.c; see fips202.h
 * in this directory.
 */

#ifndef MLK_TEST_FIPS202_FAIL_FIPS202X4_H
#define MLK_TEST_FIPS202_FAIL_FIPS202X4_H

#include "../../mlkem/src/fips202/fips202x4.h"
#include "fips202.h"

#if !defined(MLK_CONFIG_SERIAL_FIPS202_ONLY)
#undef mlk_shake128x4_absorb_once
#define mlk_shake128x4_absorb_once(state, in0, in1, in2, in3, inlen) \
  MLK_TEST_FIPS202_CALL(                                             \
      MLK_NAMESPACE(shake128x4_absorb_once)(state, in0, in1, in2, in3, inlen))

#undef mlk_shake128x4_squeezeblocks
#define mlk_shake128x4_squeezeblocks(out0, out1, out2, out3, nblocks, state) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(shake128x4_squeezeblocks)(             \
      out0, out1, out2, out3, nblocks, state))

#undef mlk_shake128x4_init
#define mlk_shake128x4_init(state) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(shake128x4_init)(state))

#undef mlk_shake128x4_release
#define mlk_shake128x4_release(state) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(shake128x4_release)(state))

#undef mlk_shake256x4
#define mlk_shake256x4(out0, out1, out2, out3, outlen, in0, in1, in2, in3, \
                       inlen)                                              \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(shake256x4)(                         \
      out0, out1, out2, out3, outlen, in0, in1, in2, in3, inlen))
#endif /* !MLK_CONFIG_SERIAL_FIPS202_ONLY */

#endif /* !MLK_TEST_FIPS202_FAIL_FIPS202X4_H */
