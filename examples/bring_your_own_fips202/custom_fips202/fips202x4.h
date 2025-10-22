/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * This is a shim establishing the FIPS-202 API required by
 * from the API exposed by tiny_sha3.
 */

#ifndef FIPS_202X4_H
#define FIPS_202X4_H

#include "tiny_sha3/sha3.h"

#include <stddef.h>
#include <stdint.h>

#include "cbmc.h"
#include "fips202.h"

typedef struct
{
  /* We introduce the explicit state as a mechanism to check that
   * mlkem-native adheres to the FIPS202 state machine. You can safely
   * remove this from your custom wrapper. */
  fips202_state_t state;
  mlk_shake128ctx ctx[4];
} mlk_shake128x4ctx;

#define mlk_shake128x4_absorb_once MLK_NAMESPACE(shake128x4_absorb_once)
static MLK_INLINE void mlk_shake128x4_absorb_once(
    mlk_shake128x4ctx *state, const uint8_t *in0, const uint8_t *in1,
    const uint8_t *in2, const uint8_t *in3, size_t inlen)
{
  assert(state->state == FIPS202_STATE_ABSORBING);
  mlk_shake128_absorb_once(&state->ctx[0], in0, inlen);
  mlk_shake128_absorb_once(&state->ctx[1], in1, inlen);
  mlk_shake128_absorb_once(&state->ctx[2], in2, inlen);
  mlk_shake128_absorb_once(&state->ctx[3], in3, inlen);
  state->state = FIPS202_STATE_SQUEEZING;
}

#define mlk_shake128x4_squeezeblocks MLK_NAMESPACE(shake128x4_squeezeblocks)
static MLK_INLINE void mlk_shake128x4_squeezeblocks(
    uint8_t *out0, uint8_t *out1, uint8_t *out2, uint8_t *out3, size_t nblocks,
    mlk_shake128x4ctx *state)
{
  assert(state->state == FIPS202_STATE_SQUEEZING);
  mlk_shake128_squeezeblocks(out0, nblocks, &state->ctx[0]);
  mlk_shake128_squeezeblocks(out1, nblocks, &state->ctx[1]);
  mlk_shake128_squeezeblocks(out2, nblocks, &state->ctx[2]);
  mlk_shake128_squeezeblocks(out3, nblocks, &state->ctx[3]);
}

#define mlk_shake128x4_init MLK_NAMESPACE(shake128x4_init)
static MLK_INLINE void mlk_shake128x4_init(mlk_shake128x4ctx *state)
{
  mlk_shake128_init(&state->ctx[0]);
  mlk_shake128_init(&state->ctx[1]);
  mlk_shake128_init(&state->ctx[2]);
  mlk_shake128_init(&state->ctx[3]);
  state->state = FIPS202_STATE_ABSORBING;
}

#define mlk_shake128x4_release MLK_NAMESPACE(shake128x4_release)
static MLK_INLINE void mlk_shake128x4_release(mlk_shake128x4ctx *state)
{
  mlk_shake128_release(&state->ctx[0]);
  mlk_shake128_release(&state->ctx[1]);
  mlk_shake128_release(&state->ctx[2]);
  mlk_shake128_release(&state->ctx[3]);
  state->state = FIPS202_STATE_RESET;
}

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
