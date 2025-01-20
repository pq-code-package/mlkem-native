/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "common.h"
#if !defined(MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED)

#include "arith_backend.h"
#include "debug.h"
#include "fips202/fips202.h"
#include "fips202/fips202x4.h"
#include "rej_uniform.h"
#include "symmetric.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define rej_uniform MLKEM_NAMESPACE(rej_uniform)
#define rej_uniform_scalar MLKEM_NAMESPACE(rej_uniform_scalar)
/* End of static namespacing */

static unsigned int rej_uniform_scalar(int16_t *r, unsigned int target,
                                       unsigned int offset, const uint8_t *buf,
                                       unsigned int buflen)
__contract__(
  requires(offset <= target && target <= 4096 && buflen <= 4096 && buflen % 3 == 0)
  requires(memory_no_alias(r, sizeof(int16_t) * target))
  requires(memory_no_alias(buf, buflen))
  requires(offset > 0 ==> array_bound(r, 0, offset, 0, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * target))
  ensures(offset <= return_value && return_value <= target)
  ensures(return_value > 0 ==> array_bound(r, 0, return_value, 0, MLKEM_Q))
)
{
  unsigned int ctr, pos;
  uint16_t val0, val1;

  debug_assert_bound(r, offset, 0, MLKEM_Q);

  ctr = offset;
  pos = 0;
  /* pos + 3 cannot overflow due to the assumption buflen <= 4096 */
  while (ctr < target && pos + 3 <= buflen)
  __loop__(
    invariant(offset <= ctr && ctr <= target && pos <= buflen)
    invariant(ctr > 0 ==> array_bound(r, 0, ctr, 0, MLKEM_Q)))
  {
    val0 = ((buf[pos + 0] >> 0) | ((uint16_t)buf[pos + 1] << 8)) & 0xFFF;
    val1 = ((buf[pos + 1] >> 4) | ((uint16_t)buf[pos + 2] << 4)) & 0xFFF;
    pos += 3;

    if (val0 < MLKEM_Q)
    {
      r[ctr++] = val0;
    }
    if (ctr < target && val1 < MLKEM_Q)
    {
      r[ctr++] = val1;
    }
  }

  debug_assert_bound(r, ctr, 0, MLKEM_Q);
  return ctr;
}

#if !defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
/*************************************************
 * Name:        rej_uniform
 *
 * Description: Run rejection sampling on uniform random bytes to generate
 *              uniform random integers mod q
 *
 * Arguments:   - int16_t *r:          pointer to output buffer
 *              - unsigned int target: requested number of 16-bit integers
 *                                     (uniform mod q).
 *                                     Must be <= 4096.
 *              - unsigned int offset: number of 16-bit integers that have
 *                                     already been sampled.
 *                                     Must be <= target.
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned int buflen: length of input buffer in bytes
 *                                     Must be <= 4096.
 *                                     Must be a multiple of 3.
 *
 * Note: Strictly speaking, only a few values of buflen near UINT_MAX need
 * excluding. The limit of 4096 is somewhat arbitary but sufficient for all
 * uses of this function. Similarly, the actual limit for target is UINT_MAX/2.
 *
 * Returns the new offset of sampled 16-bit integers, at most target,
 * and at least the initial offset.
 * If the new offset is strictly less than len, all of the input buffers
 * is guaranteed to have been consumed. If it is equal to len, no information
 * is provided on how many bytes of the input buffer have been consumed.
 **************************************************/

/*
 * NOTE: The signature differs from the Kyber reference implementation
 * in that it adds the offset and always expects the base of the target
 * buffer. This avoids shifting the buffer base in the caller, which appears
 * tricky to reason about.
 */
static unsigned int rej_uniform(int16_t *r, unsigned int target,
                                unsigned int offset, const uint8_t *buf,
                                unsigned int buflen)
__contract__(
  requires(offset <= target && target <= 4096 && buflen <= 4096 && buflen % 3 == 0)
  requires(memory_no_alias(r, sizeof(int16_t) * target))
  requires(memory_no_alias(buf, buflen))
  requires(offset > 0 ==> array_bound(r, 0, offset, 0, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * target))
  ensures(offset <= return_value && return_value <= target)
  ensures(return_value > 0 ==> array_bound(r, 0, return_value, 0, MLKEM_Q))
)
{
  return rej_uniform_scalar(r, target, offset, buf, buflen);
}
#else  /* MLKEM_USE_NATIVE_REJ_UNIFORM */
static unsigned int rej_uniform(int16_t *r, unsigned int target,
                                unsigned int offset, const uint8_t *buf,
                                unsigned int buflen)
{
  int ret;

  /* Sample from large buffer with full lane as much as possible. */
  ret = rej_uniform_native(r + offset, target - offset, buf, buflen);
  if (ret != -1)
  {
    unsigned res = offset + (unsigned)ret;
    debug_assert_bound(r, res, 0, MLKEM_Q);
    return res;
  }

  return rej_uniform_scalar(r, target, offset, buf, buflen);
}
#endif /* MLKEM_USE_NATIVE_REJ_UNIFORM */

#ifndef MLKEM_GEN_MATRIX_NBLOCKS
#define MLKEM_GEN_MATRIX_NBLOCKS \
  ((12 * MLKEM_N / 8 * (1 << 12) / MLKEM_Q + XOF_RATE) / XOF_RATE)
#endif

MLKEM_NATIVE_INTERNAL_API
void poly_rej_uniform_x4(poly *vec, uint8_t *seed[4])
{
  /* Temporary buffers for XOF output before rejection sampling */
  uint8_t buf0[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  uint8_t buf1[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  uint8_t buf2[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  uint8_t buf3[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];

  /* Tracks the number of coefficients we have already sampled */
  unsigned int ctr[KECCAK_WAY];
  xof_x4_ctx statex;
  unsigned int buflen;

  /* seed is MLKEM_SYMBYTES + 2 bytes long, but padded to MLKEM_SYMBYTES + 16 */
  xof_x4_absorb(&statex, seed[0], seed[1], seed[2], seed[3],
                MLKEM_SYMBYTES + 2);

  /*
   * Initially, squeeze heuristic number of MLKEM_GEN_MATRIX_NBLOCKS.
   * This should generate the matrix entries with high probability.
   */
  xof_x4_squeezeblocks(buf0, buf1, buf2, buf3, MLKEM_GEN_MATRIX_NBLOCKS,
                       &statex);
  buflen = MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE;
  ctr[0] = rej_uniform(vec[0].coeffs, MLKEM_N, 0, buf0, buflen);
  ctr[1] = rej_uniform(vec[1].coeffs, MLKEM_N, 0, buf1, buflen);
  ctr[2] = rej_uniform(vec[2].coeffs, MLKEM_N, 0, buf2, buflen);
  ctr[3] = rej_uniform(vec[3].coeffs, MLKEM_N, 0, buf3, buflen);

  /*
   * So long as not all matrix entries have been generated, squeeze
   * one more block a time until we're done.
   */
  buflen = XOF_RATE;
  while (ctr[0] < MLKEM_N || ctr[1] < MLKEM_N || ctr[2] < MLKEM_N ||
         ctr[3] < MLKEM_N)
  __loop__(
    assigns(ctr, statex, memory_slice(vec, sizeof(poly) * 4), object_whole(buf0),
       object_whole(buf1), object_whole(buf2), object_whole(buf3))
    invariant(ctr[0] <= MLKEM_N && ctr[1] <= MLKEM_N)
    invariant(ctr[2] <= MLKEM_N && ctr[3] <= MLKEM_N)
    invariant(ctr[0] > 0 ==> array_bound(vec[0].coeffs, 0, ctr[0], 0, MLKEM_Q))
    invariant(ctr[1] > 0 ==> array_bound(vec[1].coeffs, 0, ctr[1], 0, MLKEM_Q))
    invariant(ctr[2] > 0 ==> array_bound(vec[2].coeffs, 0, ctr[2], 0, MLKEM_Q))
    invariant(ctr[3] > 0 ==> array_bound(vec[3].coeffs, 0, ctr[3], 0, MLKEM_Q)))
  {
    xof_x4_squeezeblocks(buf0, buf1, buf2, buf3, 1, &statex);
    ctr[0] = rej_uniform(vec[0].coeffs, MLKEM_N, ctr[0], buf0, buflen);
    ctr[1] = rej_uniform(vec[1].coeffs, MLKEM_N, ctr[1], buf1, buflen);
    ctr[2] = rej_uniform(vec[2].coeffs, MLKEM_N, ctr[2], buf2, buflen);
    ctr[3] = rej_uniform(vec[3].coeffs, MLKEM_N, ctr[3], buf3, buflen);
  }

  xof_x4_release(&statex);
}

MLKEM_NATIVE_INTERNAL_API
void poly_rej_uniform(poly *entry, uint8_t seed[MLKEM_SYMBYTES + 2])
{
  xof_ctx state;
  uint8_t buf[MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE];
  unsigned int ctr, buflen;

  xof_absorb(&state, seed, MLKEM_SYMBYTES + 2);

  /* Initially, squeeze + sample heuristic number of MLKEM_GEN_MATRIX_NBLOCKS.
   */
  /* This should generate the matrix entry with high probability. */
  xof_squeezeblocks(buf, MLKEM_GEN_MATRIX_NBLOCKS, &state);
  buflen = MLKEM_GEN_MATRIX_NBLOCKS * XOF_RATE;
  ctr = rej_uniform(entry->coeffs, MLKEM_N, 0, buf, buflen);

  /* Squeeze + sample one more block a time until we're done */
  buflen = XOF_RATE;
  while (ctr < MLKEM_N)
  __loop__(
    assigns(ctr, state, memory_slice(entry, sizeof(poly)), object_whole(buf))
    invariant(ctr <= MLKEM_N)
    invariant(array_bound(entry->coeffs, 0, ctr, 0, MLKEM_Q)))
  {
    xof_squeezeblocks(buf, 1, &state);
    ctr = rej_uniform(entry->coeffs, MLKEM_N, ctr, buf, buflen);
  }

  xof_release(&state);
}

#else /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */

#define empty_cu_rej_uniform MLKEM_NAMESPACE_K(empty_cu_rej_uniform)
int empty_cu_rej_uniform;

#endif /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */
