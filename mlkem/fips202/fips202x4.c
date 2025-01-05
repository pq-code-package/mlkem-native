/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "fips202x4.h"
#include <string.h>
#include "fips202.h"
#include "keccakf1600.h"

#define shake256x4_ctx FIPS202_NAMESPACE(shake256x4_ctx)
typedef shake128x4ctx shake256x4_ctx;

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define keccak_absorb_once_x4 FIPS202_NAMESPACE(keccak_absorb_once_x4)
#define keccak_squeezeblocks_x4 FIPS202_NAMESPACE(keccak_squeezeblocks_x4)
#define shake256x4_absorb_once FIPS202_NAMESPACE(shake256x4_absorb_once)
#define shake256x4_squeezeblocks FIPS202_NAMESPACE(shake256x4_squeezeblocks)
/* End of static namespacing */

static void keccak_absorb_once_x4(uint64_t *s, uint32_t r, const uint8_t *in0,
                                  const uint8_t *in1, const uint8_t *in2,
                                  const uint8_t *in3, size_t inlen, uint8_t p)
{
  while (inlen >= r)
  {
    KeccakF1600x4_StateXORBytes(s, in0, in1, in2, in3, 0, r);
    KeccakF1600x4_StatePermute(s);

    in0 += r;
    in1 += r;
    in2 += r;
    in3 += r;
    inlen -= r;
  }

  if (inlen > 0)
  {
    KeccakF1600x4_StateXORBytes(s, in0, in1, in2, in3, 0, inlen);
  }

  if (inlen == r - 1)
  {
    p |= 128;
    KeccakF1600x4_StateXORBytes(s, &p, &p, &p, &p, inlen, 1);
  }
  else
  {
    KeccakF1600x4_StateXORBytes(s, &p, &p, &p, &p, inlen, 1);
    p = 128;
    KeccakF1600x4_StateXORBytes(s, &p, &p, &p, &p, r - 1, 1);
  }
}

static void keccak_squeezeblocks_x4(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                                    uint8_t *out3, size_t nblocks, uint64_t *s,
                                    uint32_t r)
{
  while (nblocks > 0)
  {
    KeccakF1600x4_StatePermute(s);
    KeccakF1600x4_StateExtractBytes(s, out0, out1, out2, out3, 0, r);

    out0 += r;
    out1 += r;
    out2 += r;
    out3 += r;
    nblocks--;
  }
}

void shake128x4_absorb_once(shake128x4ctx *state, const uint8_t *in0,
                            const uint8_t *in1, const uint8_t *in2,
                            const uint8_t *in3, size_t inlen)
{
  memset(state, 0, sizeof(shake128x4ctx));
  keccak_absorb_once_x4(state->ctx, SHAKE128_RATE, in0, in1, in2, in3, inlen,
                        0x1F);
}

void shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                              uint8_t *out3, size_t nblocks,
                              shake128x4ctx *state)
{
  keccak_squeezeblocks_x4(out0, out1, out2, out3, nblocks, state->ctx,
                          SHAKE128_RATE);
}

void shake128x4_release(shake128x4ctx *state) { (void)state; }

static void shake256x4_absorb_once(shake256x4_ctx *state, const uint8_t *in0,
                                   const uint8_t *in1, const uint8_t *in2,
                                   const uint8_t *in3, size_t inlen)
{
  memset(state, 0, sizeof(shake128x4ctx));
  keccak_absorb_once_x4(state->ctx, SHAKE256_RATE, in0, in1, in2, in3, inlen,
                        0x1F);
}

static void shake256x4_squeezeblocks(uint8_t *out0, uint8_t *out1,
                                     uint8_t *out2, uint8_t *out3,
                                     size_t nblocks, shake256x4_ctx *state)
{
  keccak_squeezeblocks_x4(out0, out1, out2, out3, nblocks, state->ctx,
                          SHAKE256_RATE);
}

void shake256x4(uint8_t *out0, uint8_t *out1, uint8_t *out2, uint8_t *out3,
                size_t outlen, uint8_t *in0, uint8_t *in1, uint8_t *in2,
                uint8_t *in3, size_t inlen)
{
  shake256x4_ctx statex;
  size_t nblocks = outlen / SHAKE256_RATE;
  uint8_t tmp[KECCAK_WAY][SHAKE256_RATE];

  shake256x4_absorb_once(&statex, in0, in1, in2, in3, inlen);
  shake256x4_squeezeblocks(out0, out1, out2, out3, nblocks, &statex);

  out0 += nblocks * SHAKE256_RATE;
  out1 += nblocks * SHAKE256_RATE;
  out2 += nblocks * SHAKE256_RATE;
  out3 += nblocks * SHAKE256_RATE;

  outlen -= nblocks * SHAKE256_RATE;

  if (outlen)
  {
    shake256x4_squeezeblocks(tmp[0], tmp[1], tmp[2], tmp[3], 1, &statex);
    memcpy(out0, tmp[0], outlen);
    memcpy(out1, tmp[1], outlen);
    memcpy(out2, tmp[2], outlen);
    memcpy(out3, tmp[3], outlen);
  }
}
