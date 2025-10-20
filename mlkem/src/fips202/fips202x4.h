/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_FIPS202_FIPS202X4_H
#define MLK_FIPS202_FIPS202X4_H

#include <stdint.h>

#include "../cbmc.h"
#include "../common.h"

#include "fips202.h"
#include "keccakf1600.h"

/* Context for non-incremental API */
typedef struct
{
  uint64_t ctx[MLK_KECCAK_LANES * MLK_KECCAK_WAY];
} MLK_ALIGN mlk_shake128x4ctx;

#define mlk_shake128x4_absorb_once MLK_NAMESPACE(shake128x4_absorb_once)
/*************************************************
 * Name:        mlk_shake128x4_absorb_once
 *
 * Description: 4x-batched one-shot absorb step of the SHAKE128 XOF.
 *
 *              For call-sites (in mlkem-native):
 *              - This function MUST ONLY be called straight after
 *                mlk_shake128x4_init().
 *              - This function MUST ONLY be called once.
 *
 *              Consequently, for providers of custom FIPS202 code
 *              to be used with mlkem-native:
 *              - You may assume that the input context is
 *                freshly initialized via mlk_shake128x4_init().
 *              - You may assume that this function is
 *                called exactly once.
 *
 * Arguments:   - mlk_shake128x4ctx *state:
 *                  pointer to SHAKE128x4 context
 *              - const uint8_t *in0, *in1, *in2, *in3:
 *                  pointers to inputs to be absorbed.
 *              - size_t inlen:
 *                  length of input buffers in bytes
 **************************************************/
void mlk_shake128x4_absorb_once(mlk_shake128x4ctx *state, const uint8_t *in0,
                                const uint8_t *in1, const uint8_t *in2,
                                const uint8_t *in3, size_t inlen)
__contract__(
  requires(inlen <= MLK_MAX_BUFFER_SIZE)
  requires(memory_no_alias(state, sizeof(mlk_shake128x4ctx)))
  requires(memory_no_alias(in0, inlen))
  requires(memory_no_alias(in1, inlen))
  requires(memory_no_alias(in2, inlen))
  requires(memory_no_alias(in3, inlen))
  assigns(object_whole(state))
);

#define mlk_shake128x4_squeezeblocks MLK_NAMESPACE(shake128x4_squeezeblocks)
/*************************************************
 * Name:        mlk_shake128x4_squeezeblocks
 *
 * Description: 4x-batched squeeze step of SHAKE128 XOF. Squeezes full blocks of
 *              SHAKE128_RATE bytes each. Modifies the state. Can be called
 *              multiple times to keep squeezing, i.e., is incremental.
 *
 * Arguments:   - uint8_t *out0, *out1, *out2, *out3:
 *                   pointers to output blocks
 *                   Can be assumed to be 8-byte aligned.
 *              - size_t nblocks:
 *                   number of blocks to be squeezed (written to output)
 *              - mlk_shake128x4ctx *state:  pointer to in/output Keccak state
 **************************************************/
void mlk_shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                                  uint8_t *out3, size_t nblocks,
                                  mlk_shake128x4ctx *state)
__contract__(
  requires(nblocks <= 8 /* somewhat arbitrary bound */)
  requires(memory_no_alias(state, sizeof(mlk_shake128x4ctx)))
  /* We can't express alignment of out{0,1,2,3} as a CBMC preconditions. */
  requires(memory_no_alias(out0, nblocks * SHAKE128_RATE))
  requires(memory_no_alias(out1, nblocks * SHAKE128_RATE))
  requires(memory_no_alias(out2, nblocks * SHAKE128_RATE))
  requires(memory_no_alias(out3, nblocks * SHAKE128_RATE))
  assigns(memory_slice(out0, nblocks * SHAKE128_RATE),
    memory_slice(out1, nblocks * SHAKE128_RATE),
    memory_slice(out2, nblocks * SHAKE128_RATE),
    memory_slice(out3, nblocks * SHAKE128_RATE),
    object_whole(state))
);

#define mlk_shake128x4_init MLK_NAMESPACE(shake128x4_init)
void mlk_shake128x4_init(mlk_shake128x4ctx *state);

#define mlk_shake128x4_release MLK_NAMESPACE(shake128x4_release)
void mlk_shake128x4_release(mlk_shake128x4ctx *state);

#define mlk_shake256x4 MLK_NAMESPACE(shake256x4)
/*************************************************
 * Name:        mlk_shake256x4
 *
 * Description: 4x-batched SHAKE256 XOF with non-incremental API
 *
 * Arguments:   - uint8_t *out0, *out1, *out2, *out3:
 *                  pointers to output buffers
 *                  Can be assumed to be 8-byte aligned.
 *              - size_t outlen:
 *                  requested output length in bytes
 *                  Can be assumed to be 8-byte aligned.
 *              - const uint8_t *input:
 *                  pointer to input
 *              - size_t inlen:
 *                  length of input in bytes
 **************************************************/
void mlk_shake256x4(uint8_t *out0, uint8_t *out1, uint8_t *out2, uint8_t *out3,
                    size_t outlen, uint8_t *in0, uint8_t *in1, uint8_t *in2,
                    uint8_t *in3, size_t inlen)
__contract__(
  requires(inlen <= MLK_MAX_BUFFER_SIZE)
  requires(outlen <= MLK_MAX_BUFFER_SIZE)
  /* The alignment constraint is not needed for the implementation, but
   * serves as an additional preconditions for users wishing to use an
   * alternative FIPS202 implementation. */
  requires(outlen % 8 == 0)
  requires(memory_no_alias(in0, inlen))
  requires(memory_no_alias(in1, inlen))
  requires(memory_no_alias(in2, inlen))
  requires(memory_no_alias(in3, inlen))
  /* We can't express alignment of out{0,1,2,3} as a CBMC preconditions. */
  requires(memory_no_alias(out0, outlen))
  requires(memory_no_alias(out1, outlen))
  requires(memory_no_alias(out2, outlen))
  requires(memory_no_alias(out3, outlen))
  assigns(memory_slice(out0, outlen))
  assigns(memory_slice(out1, outlen))
  assigns(memory_slice(out2, outlen))
  assigns(memory_slice(out3, outlen))
);

#endif /* !MLK_FIPS202_FIPS202X4_H */
