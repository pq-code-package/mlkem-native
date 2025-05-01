/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * This is a shim establishing the FIPS-202 API required by
 * from the API exposed by tiny_sha3.
 */

#ifndef FIPS202_H
#define FIPS202_H

#include "common.h"
#include "tiny_sha3/sha3.h"

#define SHAKE128_RATE 168
#define SHAKE256_RATE 136
#define SHA3_256_RATE 136
#define SHA3_384_RATE 104
#define SHA3_512_RATE 72

/* NOTE: This is an incremental context, different from the one used by
 * mlkem-native */
typedef sha3_ctx_t mlk_shake128ctx;

static MLK_INLINE void mlk_shake128_init(mlk_shake128ctx *state)
{
  shake128_init(state);
}

#define mlk_shake128_absorb_once MLK_NAMESPACE(shake128_absorb_once)
/*************************************************
 * Name:        mlk_shake128_absorb_once
 *
 * Description: Absorb step of the SHAKE128 XOF.
 *
 * Arguments:   - mlk_shake128ctx *state:   pointer to zeroized output Keccak
 *                                      state
 *              - const uint8_t *input: pointer to input to be absorbed into
 *                                      state
 *              - size_t inlen:         length of input in bytes
 **************************************************/
static MLK_INLINE void mlk_shake128_absorb_once(mlk_shake128ctx *state,
                                                const uint8_t *input,
                                                size_t inlen)
{
  shake_update(state, input, inlen);
  shake_xof(state);
}

/* Squeeze output out of the sponge.
 *
 * Supports being called multiple times
 */
#define mlk_shake128_squeezeblocks MLK_NAMESPACE(shake128_squeezeblocks)
/*************************************************
 * Name:        mlk_shake128_squeezeblocks
 *
 * Description: Squeeze step of SHAKE128 XOF. Squeezes full blocks of
 *              SHAKE128_RATE bytes each. Modifies the state. Can be called
 *              multiple times to keep squeezing, i.e., is incremental.
 *
 * Arguments:   - uint8_t *output:     pointer to output blocks
 *              - size_t nblocks:      number of blocks to be squeezed (written
 *                                     to output)
 *              - mlk_shake128ctx *state:  pointer to in/output Keccak state
 **************************************************/
static MLK_INLINE void mlk_shake128_squeezeblocks(uint8_t *output,
                                                  size_t nblocks,
                                                  mlk_shake128ctx *state)
{
  shake_out(state, output, nblocks * SHAKE128_RATE);
}

/* Free the state */
#define mlk_shake128_release MLK_NAMESPACE(shake128_release)
static MLK_INLINE void mlk_shake128_release(mlk_shake128ctx *state)
{
  ((void)state);
}

/* One-stop SHAKE256 call. Aliasing between input and
 * output is not permitted */
#define mlk_shake256 MLK_NAMESPACE(shake256)
/*************************************************
 * Name:        mlk_shake256
 *
 * Description: SHAKE256 XOF with non-incremental API
 *
 * Arguments:   - uint8_t *output:      pointer to output
 *              - size_t outlen:        requested output length in bytes
 *              - const uint8_t *input: pointer to input
 *              - size_t inlen:         length of input in bytes
 **************************************************/
static MLK_INLINE void mlk_shake256(uint8_t *output, size_t outlen,
                                    const uint8_t *input, size_t inlen)
{
  sha3_ctx_t c;
  shake256_init(&c);
  shake_update(&c, input, inlen);
  shake_xof(&c);
  shake_out(&c, output, outlen);
}

/* One-stop SHA3_256 call. Aliasing between input and
 * output is not permitted */
#define SHA3_256_HASHBYTES 32
#define mlk_sha3_256 MLK_NAMESPACE(sha3_256)
/*************************************************
 * Name:        mlk_sha3_256
 *
 * Description: SHA3-256 with non-incremental API
 *
 * Arguments:   - uint8_t *output:      pointer to output
 *              - const uint8_t *input: pointer to input
 *              - size_t inlen:         length of input in bytes
 **************************************************/
static MLK_INLINE void mlk_sha3_256(uint8_t *output, const uint8_t *input,
                                    size_t inlen)
{
  (void)sha3(input, inlen, output, SHA3_256_HASHBYTES);
}

/* One-stop SHA3_512 call. Aliasing between input and
 * output is not permitted */
#define SHA3_512_HASHBYTES 64
#define mlk_sha3_512 MLK_NAMESPACE(sha3_512)
/*************************************************
 * Name:        mlk_sha3_512
 *
 * Description: SHA3-512 with non-incremental API
 *
 * Arguments:   - uint8_t *output:      pointer to output
 *              - const uint8_t *input: pointer to input
 *              - size_t inlen:         length of input in bytes
 **************************************************/
static MLK_INLINE void mlk_sha3_512(uint8_t *output, const uint8_t *input,
                                    size_t inlen)
{
  (void)sha3(input, inlen, output, SHA3_512_HASHBYTES);
}

#endif /* !FIPS202_H */
