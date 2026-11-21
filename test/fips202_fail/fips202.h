/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Custom FIPS202 header for test/src/test_fips202_fail.c.
 *
 * It uses the FIPS202 implementation shipped with mlkem-native, but lets the
 * test make any call fail, including the init and release functions. See
 * MLK_CONFIG_FIPS202_CAN_FAIL.
 */

#ifndef MLK_TEST_FIPS202_FAIL_FIPS202_H
#define MLK_TEST_FIPS202_FAIL_FIPS202_H

#include "../../mlkem/src/fips202/fips202.h"

/* Returns non-zero if the current FIPS202 call should fail; defined in
 * test/src/test_fips202_fail.c. */
int mlk_test_fips202_fail(void);

#define MLK_TEST_FIPS202_CALL(call) (mlk_test_fips202_fail() ? -1 : (call))

#undef mlk_shake128_absorb_once
#define mlk_shake128_absorb_once(state, input, inlen) \
  MLK_TEST_FIPS202_CALL(                              \
      MLK_NAMESPACE(shake128_absorb_once)(state, input, inlen))

#undef mlk_shake128_squeezeblocks
#define mlk_shake128_squeezeblocks(output, nblocks, state) \
  MLK_TEST_FIPS202_CALL(                                   \
      MLK_NAMESPACE(shake128_squeezeblocks)(output, nblocks, state))

#undef mlk_shake128_init
#define mlk_shake128_init(state) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(shake128_init)(state))

#undef mlk_shake128_release
#define mlk_shake128_release(state) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(shake128_release)(state))

#undef mlk_shake256
#define mlk_shake256(output, outlen, input, inlen) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(shake256)(output, outlen, input, inlen))

#undef mlk_sha3_256
#define mlk_sha3_256(output, input, inlen) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(sha3_256)(output, input, inlen))

#undef mlk_sha3_512
#define mlk_sha3_512(output, input, inlen) \
  MLK_TEST_FIPS202_CALL(MLK_NAMESPACE(sha3_512)(output, input, inlen))

#endif /* !MLK_TEST_FIPS202_FAIL_FIPS202_H */
