/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_FIPS202_FIPS202_H
#define MLK_FIPS202_FIPS202_H
#include <stddef.h>
#include <stdint.h>
#include "../cbmc.h"
#include "../common.h"

#define SHAKE128_RATE 168
#define SHAKE256_RATE 136
#define SHA3_256_RATE 136
#define SHA3_384_RATE 104
#define SHA3_512_RATE 72

/* Context for non-incremental API */
#define shake128ctx MLK_NAMESPACE(shake128ctx)
typedef struct
{
  uint64_t ctx[25];
} shake128ctx;

#define shake128_absorb_once MLK_NAMESPACE(shake128_absorb_once)
/*************************************************
 * Name:        shake128_absorb_once
 *
 * Description: One-shot absorb step of the SHAKE128 XOF.
 *
 *              For call-sites (in mlkem-native):
 *              - This function MUST ONLY be called straight after
 *                shake128_init().
 *              - This function MUST ONLY be called once.
 *
 *              Consequently, for providers of custom FIPS202 code
 *              to be used with mlkem-native:
 *              - You may assume that the input context is
 *                freshly initialized via shake128_init().
 *              - You may assume that this function is
 *                called exactly once.
 *
 * Arguments:   - shake128ctx *state:   pointer to SHAKE128 context
 *              - const uint8_t *input: pointer to input to be absorbed into
 *                                      the state
 *              - size_t inlen:         length of input in bytes
 **************************************************/
void shake128_absorb_once(shake128ctx *state, const uint8_t *input,
                          size_t inlen)
__contract__(
  requires(memory_no_alias(state, sizeof(shake128ctx)))
  requires(memory_no_alias(input, inlen))
  assigns(memory_slice(state, sizeof(shake128ctx)))
);

#define shake128_squeezeblocks MLK_NAMESPACE(shake128_squeezeblocks)
/*************************************************
 * Name:        shake128_squeezeblocks
 *
 * Description: Squeeze step of SHAKE128 XOF. Squeezes full blocks of
 *              SHAKE128_RATE bytes each. Modifies the state. Can be called
 *              multiple times to keep squeezing, i.e., is incremental.
 *
 * Arguments:   - uint8_t *output:     pointer to output blocks
 *              - size_t nblocks:      number of blocks to be squeezed (written
 *                                     to output)
 *              - shake128ctx *state:  pointer to in/output Keccak state
 **************************************************/
void shake128_squeezeblocks(uint8_t *output, size_t nblocks, shake128ctx *state)
__contract__(
  requires(nblocks <= 8 /* somewhat arbitrary bound */)
  requires(memory_no_alias(state, sizeof(shake128ctx)))
  requires(memory_no_alias(output, nblocks * SHAKE128_RATE))
  assigns(memory_slice(output, nblocks * SHAKE128_RATE), memory_slice(state, sizeof(shake128ctx)))
);

#define shake128_init MLK_NAMESPACE(shake128_init)
void shake128_init(shake128ctx *state);

#define shake128_release MLK_NAMESPACE(shake128_release)
void shake128_release(shake128ctx *state);

/* One-stop SHAKE256 call. Aliasing between input and
 * output is not permitted */
#define shake256 MLK_NAMESPACE(shake256)
/*************************************************
 * Name:        shake256
 *
 * Description: SHAKE256 XOF with non-incremental API
 *
 * Arguments:   - uint8_t *output:      pointer to output
 *              - size_t outlen:        requested output length in bytes
 *              - const uint8_t *input: pointer to input
 *              - size_t inlen:         length of input in bytes
 **************************************************/
void shake256(uint8_t *output, size_t outlen, const uint8_t *input,
              size_t inlen)
__contract__(
  requires(memory_no_alias(input, inlen))
  requires(memory_no_alias(output, outlen))
  assigns(memory_slice(output, outlen))
);

/* One-stop SHA3_256 call. Aliasing between input and
 * output is not permitted */
#define SHA3_256_HASHBYTES 32
#define sha3_256 MLK_NAMESPACE(sha3_256)
/*************************************************
 * Name:        sha3_256
 *
 * Description: SHA3-256 with non-incremental API
 *
 * Arguments:   - uint8_t *output:      pointer to output
 *              - const uint8_t *input: pointer to input
 *              - size_t inlen:         length of input in bytes
 **************************************************/
void sha3_256(uint8_t *output, const uint8_t *input, size_t inlen)
__contract__(
  requires(memory_no_alias(input, inlen))
  requires(memory_no_alias(output, SHA3_256_HASHBYTES))
  assigns(memory_slice(output, SHA3_256_HASHBYTES))
);

/* One-stop SHA3_512 call. Aliasing between input and
 * output is not permitted */
#define SHA3_512_HASHBYTES 64
#define sha3_512 MLK_NAMESPACE(sha3_512)
/*************************************************
 * Name:        sha3_512
 *
 * Description: SHA3-512 with non-incremental API
 *
 * Arguments:   - uint8_t *output:      pointer to output
 *              - const uint8_t *input: pointer to input
 *              - size_t inlen:         length of input in bytes
 **************************************************/
void sha3_512(uint8_t *output, const uint8_t *input, size_t inlen)
__contract__(
  requires(memory_no_alias(input, inlen))
  requires(memory_no_alias(output, SHA3_512_HASHBYTES))
  assigns(memory_slice(output, SHA3_512_HASHBYTES))
);

#include "fips202_backend.h"
#if !defined(MLK_FIPS202_BACKEND_IMPL) ||   \
    (!defined(MLK_USE_FIPS202_X2_NATIVE) && \
     !defined(MLK_USE_FIPS202_X4_NATIVE))
/* If you provide your own FIPS-202 implementation where the x4-
 * Keccak-f1600-x4 implementation falls back to 4-fold Keccak-f1600,
 * set this to gain a small speedup. */
#define FIPS202_X4_DEFAULT_IMPLEMENTATION
#endif


#endif /* MLK_FIPS202_FIPS202_H */
