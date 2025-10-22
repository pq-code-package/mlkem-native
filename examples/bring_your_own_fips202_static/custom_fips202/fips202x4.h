/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef FIPS_202X4_H
#define FIPS_202X4_H

#include <stdint.h>

#include "fips202.h"

/*
 * The incremental batched APIs are not required for this example since
 * we build with MLK_CONFIG_SERIAL_FIPS202_ONLY. We still need the one-shot
 * batched API, but it just falls back to the unbatched API.
 */

#define mlk_shake256x4 MLK_NAMESPACE(shake256x4)
static MLK_INLINE void mlk_shake256x4(uint8_t *out0, uint8_t *out1,
                                      uint8_t *out2, uint8_t *out3,
                                      size_t outlen, uint8_t *in0, uint8_t *in1,
                                      uint8_t *in2, uint8_t *in3, size_t inlen)
{
  mlk_shake256(out0, outlen, in0, inlen);
  mlk_shake256(out1, outlen, in1, inlen);
  mlk_shake256(out2, outlen, in2, inlen);
  mlk_shake256(out3, outlen, in3, inlen);
}

#endif /* !FIPS_202X4_H */
