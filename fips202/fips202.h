// SPDX-License-Identifier: CC0-1.0
#ifndef FIPS202_H
#define FIPS202_H

#include <stddef.h>
#include <stdint.h>
#include "namespace.h"

#include "cbmc.h"

#define SHAKE128_RATE 168
#define SHAKE256_RATE 136
#define SHA3_256_RATE 136
#define SHA3_384_RATE 104
#define SHA3_512_RATE 72


// Context for non-incremental API
typedef struct {
  uint64_t ctx[25];
} shake128ctx;

// Context for incremental API
typedef struct {
  uint64_t ctx[26];
} shake256incctx;

/* Initialize the state and absorb the provided input.
 *
 * This function does not support being called multiple times
 * with the same state.
 */
#define shake128_absorb FIPS202_NAMESPACE(shake128_absorb)
void shake128_absorb(shake128ctx *state, const uint8_t *input, size_t inlen)
    // clang-format off
REQUIRES(IS_FRESH(state, sizeof(shake128ctx)))
REQUIRES(IS_FRESH(input, inlen)) ASSIGNS(OBJECT_WHOLE(state));
// clang-format on

/* Squeeze output out of the sponge.
 *
 * Supports being called multiple times
 */
#define shake128_squeezeblocks FIPS202_NAMESPACE(shake128_squeezeblocks)
void shake128_squeezeblocks(uint8_t *output, size_t nblocks, shake128ctx *state)
    // clang-format off
REQUIRES(IS_FRESH(state, sizeof(shake128ctx)))
REQUIRES(IS_FRESH(output, nblocks *SHAKE128_RATE))
ASSIGNS(OBJECT_WHOLE(output), OBJECT_WHOLE(state));
// clang-format on


/* Free the state */
#define shake128_ctx_release FIPS202_NAMESPACE(shake128_ctx_release)
void shake128_ctx_release(shake128ctx *state);

/* Initialize incremental hashing API */
#define shake256_inc_init FIPS202_NAMESPACE(shake256_inc_init)
void shake256_inc_init(shake256incctx *state);
#define shake256_inc_absorb FIPS202_NAMESPACE(shake256_inc_absorb)
void shake256_inc_absorb(shake256incctx *state, const uint8_t *input,
                         size_t inlen);
/* Prepares for squeeze phase */
#define shake256_inc_finalize FIPS202_NAMESPACE(shake256_inc_finalize)
void shake256_inc_finalize(shake256incctx *state);

/* Squeeze output out of the sponge.
 *
 * Supports being called multiple times
 */
#define shake256_inc_squeeze FIPS202_NAMESPACE(shake256_inc_squeeze)
void shake256_inc_squeeze(uint8_t *output, size_t outlen,
                          shake256incctx *state);

/* Free the state */
#define shake256_inc_ctx_release FIPS202_NAMESPACE(shake256_inc_ctx_release)
void shake256_inc_ctx_release(shake256incctx *state);

/* One-stop SHAKE256 call */
#define shake256 FIPS202_NAMESPACE(shake256)
void shake256(uint8_t *output, size_t outlen, const uint8_t *input,
              size_t inlen)  // clang-format off
// Refine +prove this spec, e.g. add disjointness constraints?
REQUIRES(READABLE(input, inlen))
REQUIRES(WRITEABLE(output, outlen))
ASSIGNS(OBJECT_UPTO(output, outlen));
// clang-format on

/* One-stop SHA3-256 shop */
#define sha3_256 FIPS202_NAMESPACE(sha3_256)
void sha3_256(uint8_t *output, const uint8_t *input, size_t inlen)
    // clang-format off
REQUIRES(IS_FRESH(input, inlen))
REQUIRES(IS_FRESH(output, 32))
ASSIGNS(OBJECT_WHOLE(output));
// clang-format on

/* One-stop SHA3-512 shop */
#define sha3_512 FIPS202_NAMESPACE(sha3_512)
void sha3_512(uint8_t *output, const uint8_t *input, size_t inlen)
    // clang-format off
REQUIRES(
    /* Case A: Aliasing between input and output */
    (output == input && inlen <= 64 && IS_FRESH(output, 64))
 ||
    /* Case B: Disjoint input and output */
    (IS_FRESH(input, inlen) && IS_FRESH(output, 64))
)
ASSIGNS(OBJECT_WHOLE(output));
// clang-format on

#endif
