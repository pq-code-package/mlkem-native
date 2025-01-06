
/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
/* Based on the CC0 implementation in https://github.com/mupq/mupq and
 * the public domain implementation in
 * crypto_hash/keccakc512/simple/ from http://bench.cr.yp.to/supercop.html
 * by Ronny Van Keer
 * and the public domain "TweetFips202" implementation
 * from https://twitter.com/tweetfips202
 * by Gilles Van Assche, Daniel J. Bernstein, and Peter Schwabe */

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "fips202.h"
#include "keccakf1600.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define keccak_absorb_once FIPS202_NAMESPACE(keccak_absorb_once)
#define keccak_squeeze_once FIPS202_NAMESPACE(keccak_squeeze_once)
#define keccak_squeezeblocks FIPS202_NAMESPACE(keccak_squeezeblocks)
/* End of static namespacing */

/*************************************************
 * Name:        keccak_absorb_once
 *
 * Description: Absorb step of Keccak;
 *              non-incremental, starts by zeroeing the state.
 *
 *              WARNING: Must only be called once.
 *
 * Arguments:   - uint64_t *s:       pointer to (uninitialized) output Keccak
 *                                   state
 *              - uint32_t r:        rate in bytes (e.g., 168 for SHAKE128)
 *              - const uint8_t *m:  pointer to input to be absorbed into s
 *              - size_t mlen:       length of input in bytes
 *              - uint8_t p:         domain-separation byte for different
 *                                   Keccak-derived functions
 **************************************************/
static void keccak_absorb_once(uint64_t *s, uint32_t r, const uint8_t *m,
                               size_t mlen, uint8_t p)
__contract__(
    requires(r <= sizeof(uint64_t) * KECCAK_LANES)
    requires(memory_no_alias(s, sizeof(uint64_t) * KECCAK_LANES))
    requires(memory_no_alias(m, mlen))
    assigns(memory_slice(s, sizeof(uint64_t) * KECCAK_LANES)))
{
  /* Initialize state */
  size_t i;
  for (i = 0; i < 25; ++i)
  __loop__(invariant(i <= 25))
  {
    s[i] = 0;
  }

  while (mlen >= r)
  __loop__(
    assigns(mlen, m, memory_slice(s, sizeof(uint64_t) * KECCAK_LANES))
    invariant(mlen <= loop_entry(mlen))
    invariant(m == loop_entry(m) + (loop_entry(mlen) - mlen)))
  {
    KeccakF1600_StateXORBytes(s, m, 0, r);
    KeccakF1600_StatePermute(s);
    mlen -= r;
    m += r;
  }

  if (mlen > 0)
  {
    KeccakF1600_StateXORBytes(s, m, 0, mlen);
  }

  if (mlen == r - 1)
  {
    p |= 128;
    KeccakF1600_StateXORBytes(s, &p, mlen, 1);
  }
  else
  {
    KeccakF1600_StateXORBytes(s, &p, mlen, 1);
    p = 128;
    KeccakF1600_StateXORBytes(s, &p, r - 1, 1);
  }
}

/*************************************************
 * Name:        keccak_squeezeblocks
 *
 * Description: block-level Keccak squeeze
 *
 * Arguments:   - uint8_t *h: pointer to output bytes
 *              - size_t nblocks: number of blocks to be squeezed
 *              - uint64_t *s_inc: pointer to input/output state
 *              - uint32_t r: rate in bytes (e.g., 168 for SHAKE128)
 **************************************************/
static void keccak_squeezeblocks(uint8_t *h, size_t nblocks, uint64_t *s,
                                 uint32_t r)
__contract__(
    requires(r <= sizeof(uint64_t) * KECCAK_LANES)
    requires(nblocks <= 8 /* somewhat arbitrary bound */)
    requires(memory_no_alias(s, sizeof(uint64_t) * KECCAK_LANES))
    requires(memory_no_alias(h, nblocks * r))
    assigns(memory_slice(s, sizeof(uint64_t) * KECCAK_LANES))
    assigns(memory_slice(h, nblocks *r)))
{
  while (nblocks > 0)
  __loop__(
    assigns(h, nblocks,
      memory_slice(s, sizeof(uint64_t) * KECCAK_LANES),
      memory_slice(h, nblocks * r))
    invariant(nblocks <= loop_entry(nblocks) &&
      h == loop_entry(h) + r * (loop_entry(nblocks) - nblocks)))
  {
    KeccakF1600_StatePermute(s);
    KeccakF1600_StateExtractBytes(s, h, 0, r);
    h += r;
    nblocks--;
  }
}

/*************************************************
 * Name:        keccak_squeeze_once
 *
 * Description: Keccak squeeze; can be called on byte-level
 *
 *              WARNING: This must only be called once.
 *
 * Arguments:   - uint8_t *h: pointer to output bytes
 *              - size_t outlen: number of bytes to be squeezed
 *              - uint64_t *s_inc: pointer to Keccak state
 *              - uint32_t r: rate in bytes (e.g., 168 for SHAKE128)
 **************************************************/
static void keccak_squeeze_once(uint8_t *h, size_t outlen, uint64_t *s,
                                uint32_t r)
__contract__(
    requires(r <= sizeof(uint64_t) * KECCAK_LANES)
    requires(memory_no_alias(s, sizeof(uint64_t) * KECCAK_LANES))
    requires(memory_no_alias(h, outlen))
    assigns(memory_slice(s, sizeof(uint64_t) * KECCAK_LANES))
    assigns(memory_slice(h, outlen)))
{
  size_t len;
  while (outlen > 0)
  __loop__(
    assigns(len, h, outlen,
      memory_slice(s, sizeof(uint64_t) * KECCAK_LANES),
      memory_slice(h, outlen))
    invariant(outlen <= loop_entry(outlen) &&
      h == loop_entry(h) + (loop_entry(outlen) - outlen)))
  {
    KeccakF1600_StatePermute(s);

    if (outlen < r)
    {
      len = outlen;
    }
    else
    {
      len = r;
    }
    KeccakF1600_StateExtractBytes(s, h, 0, len);
    h += len;
    outlen -= len;
  }
}

void shake128_absorb_once(shake128ctx *state, const uint8_t *input,
                          size_t inlen)
{
  keccak_absorb_once(state->ctx, SHAKE128_RATE, input, inlen, 0x1F);
}

void shake128_squeezeblocks(uint8_t *output, size_t nblocks, shake128ctx *state)
{
  keccak_squeezeblocks(output, nblocks, state->ctx, SHAKE128_RATE);
}

void shake128_release(shake128ctx *state) { (void)state; }

#define shake256ctx FIPS202_NAMESPACE(shake256ctx)
typedef shake128ctx shake256ctx;
void shake256(uint8_t *output, size_t outlen, const uint8_t *input,
              size_t inlen)
{
  shake256ctx state;
  /* Absorb input */
  keccak_absorb_once(state.ctx, SHAKE256_RATE, input, inlen, 0x1F);
  /* Squeeze output */
  keccak_squeeze_once(output, outlen, state.ctx, SHAKE256_RATE);
}

void sha3_256(uint8_t *output, const uint8_t *input, size_t inlen)
{
  uint64_t ctx[25];
  /* Absorb input */
  keccak_absorb_once(ctx, SHA3_256_RATE, input, inlen, 0x06);
  /* Squeeze output */
  keccak_squeeze_once(output, 32, ctx, SHA3_256_RATE);
}

void sha3_512(uint8_t *output, const uint8_t *input, size_t inlen)
{
  uint64_t ctx[25];
  /* Absorb input */
  keccak_absorb_once(ctx, SHA3_512_RATE, input, inlen, 0x06);
  /* Squeeze output */
  keccak_squeeze_once(output, 64, ctx, SHA3_512_RATE);
}
