/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef KECCAKF1600_H
#define KECCAKF1600_H
#include <stdint.h>
#include "../cbmc.h"
#include "../common.h"
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
                                   unsigned int offset, unsigned int length)
__contract__(
    requires(0 <= offset && offset <= KECCAK_LANES * sizeof(uint64_t) &&
	     0 <= length && length <= KECCAK_LANES * sizeof(uint64_t) - offset)
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES))
    requires(memory_no_alias(data, length))
    assigns(memory_slice(data, length))
);

#define KeccakF1600_StateXORBytes FIPS202_NAMESPACE(KeccakF1600_StateXORBytes)
void KeccakF1600_StateXORBytes(uint64_t *state, const unsigned char *data,
                               unsigned int offset, unsigned int length)
__contract__(
    requires(0 <= offset && offset <= KECCAK_LANES * sizeof(uint64_t) &&
	     0 <= length && length <= KECCAK_LANES * sizeof(uint64_t) - offset)
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES))
    requires(memory_no_alias(data, length))
    assigns(memory_slice(state, sizeof(uint64_t) * KECCAK_LANES))
);

#define KeccakF1600x4_StateExtractBytes \
  FIPS202_NAMESPACE(KeccakF1600x4_StateExtractBytes)
void KeccakF1600x4_StateExtractBytes(uint64_t *state, unsigned char *data0,
                                     unsigned char *data1, unsigned char *data2,
                                     unsigned char *data3, unsigned int offset,
                                     unsigned int length)
__contract__(
    requires(0 <= offset && offset <= KECCAK_LANES * sizeof(uint64_t) &&
	     0 <= length && length <= KECCAK_LANES * sizeof(uint64_t) - offset)
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES * KECCAK_WAY))
    requires(memory_no_alias(data0, length))
    requires(memory_no_alias(data1, length))
    requires(memory_no_alias(data2, length))
    requires(memory_no_alias(data3, length))
    assigns(memory_slice(data0, length))
    assigns(memory_slice(data1, length))
    assigns(memory_slice(data2, length))
    assigns(memory_slice(data3, length))
);

#define KeccakF1600x4_StateXORBytes \
  FIPS202_NAMESPACE(KeccakF1600x4_StateXORBytes)
void KeccakF1600x4_StateXORBytes(uint64_t *state, const unsigned char *data0,
                                 const unsigned char *data1,
                                 const unsigned char *data2,
                                 const unsigned char *data3,
                                 unsigned int offset, unsigned int length)
__contract__(
    requires(0 <= offset && offset <= KECCAK_LANES * sizeof(uint64_t) &&
	     0 <= length && length <= KECCAK_LANES * sizeof(uint64_t) - offset)
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES * KECCAK_WAY))
    requires(memory_no_alias(data0, length))
    /* Case 1: all input buffers are distinct; Case 2: All input buffers are the same */
    requires((data0 == data1 &&
              data0 == data2 &&
              data0 == data3) ||
	     (memory_no_alias(data1, length) &&
              memory_no_alias(data2, length) &&
              memory_no_alias(data3, length)))
    assigns(memory_slice(state, sizeof(uint64_t) * KECCAK_LANES * KECCAK_WAY))
);


#define KeccakF1600x4_StatePermute FIPS202_NAMESPACE(KeccakF1600x4_StatePermute)
void KeccakF1600x4_StatePermute(uint64_t *state)
__contract__(
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES * KECCAK_WAY))
    assigns(memory_slice(state, sizeof(uint64_t) * KECCAK_LANES * KECCAK_WAY))
);


#if !defined(MLKEM_USE_FIPS202_X1_ASM)
#define KeccakF1600_StatePermute FIPS202_NAMESPACE(KeccakF1600_StatePermute)
void KeccakF1600_StatePermute(uint64_t *state)
__contract__(
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES))
    assigns(memory_slice(state, sizeof(uint64_t) * KECCAK_LANES))
);

#else
#define KeccakF1600_StatePermute FIPS202_NAMESPACE(keccak_f1600_x1_asm)
#endif

#endif /* KECCAKF1600_H */
