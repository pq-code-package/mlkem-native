/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
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

typedef shake128ctx shake128x4ctx[4];

#define shake128x4_absorb_once MLKEM_NAMESPACE(shake128x4_absorb_once)
static INLINE void shake128x4_absorb_once(shake128x4ctx *state,
                                          const uint8_t *in0,
                                          const uint8_t *in1,
                                          const uint8_t *in2,
                                          const uint8_t *in3, size_t inlen)
__contract__(
  requires(memory_no_alias(state, sizeof(shake128x4ctx)))
  requires(memory_no_alias(in0, inlen))
  requires(memory_no_alias(in1, inlen))
  requires(memory_no_alias(in2, inlen))
  requires(memory_no_alias(in3, inlen))
  assigns(object_whole(state))
)
{
  shake128_absorb_once(&(*state)[0], in0, inlen);
  shake128_absorb_once(&(*state)[1], in1, inlen);
  shake128_absorb_once(&(*state)[2], in2, inlen);
  shake128_absorb_once(&(*state)[3], in3, inlen);
}

#define shake128x4_squeezeblocks MLKEM_NAMESPACE(shake128x4_squeezeblocks)
static INLINE void shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1,
                                            uint8_t *out2, uint8_t *out3,
                                            size_t nblocks,
                                            shake128x4ctx *state)
__contract__(
  requires(memory_no_alias(state, sizeof(shake128x4ctx)))
  requires(memory_no_alias(out0, nblocks * SHAKE128_RATE))
  requires(memory_no_alias(out1, nblocks * SHAKE128_RATE))
  requires(memory_no_alias(out2, nblocks * SHAKE128_RATE))
  requires(memory_no_alias(out3, nblocks * SHAKE128_RATE))
  assigns(memory_slice(out0, nblocks * SHAKE128_RATE),
    memory_slice(out1, nblocks * SHAKE128_RATE),
    memory_slice(out2, nblocks * SHAKE128_RATE),
    memory_slice(out3, nblocks * SHAKE128_RATE),
    object_whole(state))
)
{
  shake128_squeezeblocks(out0, nblocks, &(*state)[0]);
  shake128_squeezeblocks(out1, nblocks, &(*state)[1]);
  shake128_squeezeblocks(out2, nblocks, &(*state)[2]);
  shake128_squeezeblocks(out3, nblocks, &(*state)[3]);
}

#define shake128x4_release MLKEM_NAMESPACE(shake128x4_release)
static INLINE void shake128x4_release(shake128x4ctx *state)
{
  shake128_release(&(*state)[0]);
  shake128_release(&(*state)[1]);
  shake128_release(&(*state)[2]);
  shake128_release(&(*state)[3]);
}

#define shake256x4 MLKEM_NAMESPACE(shake256x4)
static INLINE void shake256x4(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                              uint8_t *out3, size_t outlen, uint8_t *in0,
                              uint8_t *in1, uint8_t *in2, uint8_t *in3,
                              size_t inlen)
__contract__(
/* Refine +prove this spec, e.g. add disjointness constraints? */
  requires(readable(in0, inlen))
  requires(readable(in1, inlen))
  requires(readable(in2, inlen))
  requires(readable(in3, inlen))
  requires(writeable(out0, outlen))
  requires(writeable(out1, outlen))
  requires(writeable(out2, outlen))
  requires(writeable(out3, outlen))
  assigns(memory_slice(out0, outlen))
  assigns(memory_slice(out1, outlen))
  assigns(memory_slice(out2, outlen))
  assigns(memory_slice(out3, outlen))
)
{
  shake256(out0, outlen, in0, inlen);
  shake256(out1, outlen, in1, inlen);
  shake256(out2, outlen, in2, inlen);
  shake256(out3, outlen, in3, inlen);
}

#endif
