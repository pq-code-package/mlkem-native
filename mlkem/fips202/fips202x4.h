/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef FIPS_202X4_H
#define FIPS_202X4_H

#include <stddef.h>
#include <stdint.h>
#include "common.h"
#include "fips202.h"
#include "keccakf1600.h"

#include "cbmc.h"

/* Context for non-incremental API */
#define shake128x4ctx FIPS202_NAMESPACE(shake128x4ctx)
typedef struct
{
  uint64_t ctx[KECCAK_LANES * KECCAK_WAY];
} shake128x4ctx;

#define shake128x4_absorb_once FIPS202_NAMESPACE(shake128x4_absorb_once)
void shake128x4_absorb_once(shake128x4ctx *state, const uint8_t *in0,
                            const uint8_t *in1, const uint8_t *in2,
                            const uint8_t *in3, size_t inlen)
__contract__(
  requires(memory_no_alias(state, sizeof(shake128x4ctx)))
  requires(memory_no_alias(in0, inlen))
  requires(memory_no_alias(in1, inlen))
  requires(memory_no_alias(in2, inlen))
  requires(memory_no_alias(in3, inlen))
  assigns(object_whole(state))
);

#define shake128x4_squeezeblocks FIPS202_NAMESPACE(shake128x4_squeezeblocks)
void shake128x4_squeezeblocks(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                              uint8_t *out3, size_t nblocks,
                              shake128x4ctx *state)
__contract__(
  requires(nblocks <= 8 /* somewhat arbitrary bound */)
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
);

#define shake128x4_release FIPS202_NAMESPACE(shake128x4_release)
void shake128x4_release(shake128x4ctx *state);

#define shake256x4 FIPS202_NAMESPACE(shake256x4)
void shake256x4(uint8_t *out0, uint8_t *out1, uint8_t *out2, uint8_t *out3,
                size_t outlen, uint8_t *in0, uint8_t *in1, uint8_t *in2,
                uint8_t *in3, size_t inlen)
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
);

#endif
