/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef KECCAKF1600_H
#define KECCAKF1600_H

#include <stdint.h>
#include "fips202_native.h"
#include "namespace.h"

#define KECCAK_WAY 4
#define KECCAK_LANES 25

/*
 * WARNING:
 * The contents of this structure, including the placement
 * and interleaving of Keccak lanes, are IMPLEMENTATION-DEFINED.
 * The struct is only exposed here to allow its construction on the stack.
 */

#define KeccakF1600_StateExtractBytes \
  FIPS202_NAMESPACE(KeccakF1600_StateExtractBytes)
void KeccakF1600_StateExtractBytes(uint64_t *state, unsigned char *data,
                                   unsigned int offset, unsigned int length);

#define KeccakF1600_StateXORBytes FIPS202_NAMESPACE(KeccakF1600_StateXORBytes)
void KeccakF1600_StateXORBytes(uint64_t *state, const unsigned char *data,
                               unsigned int offset, unsigned int length);

#define KeccakF1600x4_StateExtractBytes \
  FIPS202_NAMESPACE(KeccakF1600x4_StateExtractBytes)
void KeccakF1600x4_StateExtractBytes(uint64_t *state, unsigned char *data0,
                                     unsigned char *data1, unsigned char *data2,
                                     unsigned char *data3, unsigned int offset,
                                     unsigned int length);

#define KeccakF1600x4_StateXORBytes \
  FIPS202_NAMESPACE(KeccakF1600x4_StateXORBytes)
void KeccakF1600x4_StateXORBytes(uint64_t *state, const unsigned char *data0,
                                 const unsigned char *data1,
                                 const unsigned char *data2,
                                 const unsigned char *data3,
                                 unsigned int offset, unsigned int length);

#define KeccakF1600x4_StatePermute FIPS202_NAMESPACE(KeccakF1600x4_StatePermute)
void KeccakF1600x4_StatePermute(uint64_t *state);

#if !defined(MLKEM_USE_FIPS202_X1_ASM)
#define KeccakF1600_StatePermute FIPS202_NAMESPACE(KeccakF1600_StatePermute)
void KeccakF1600_StatePermute(uint64_t *state);
#else
#define KeccakF1600_StatePermute FIPS202_NAMESPACE(keccak_f1600_x1_asm)
#endif

#endif
