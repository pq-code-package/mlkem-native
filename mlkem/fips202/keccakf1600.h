/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_FIPS202_KECCAKF1600_H
#define MLK_FIPS202_KECCAKF1600_H
#include <stdint.h>
#include "../cbmc.h"
#include "../common.h"

#define KECCAK_LANES 25
#define KECCAK_WAY 4

/*
 * WARNING:
 * The contents of this structure, including the placement
 * and interleaving of Keccak lanes, are IMPLEMENTATION-DEFINED.
 * The struct is only exposed here to allow its construction on the stack.
 */

#define KeccakF1600_StateExtractBytes \
  MLK_NAMESPACE(KeccakF1600_StateExtractBytes)
void KeccakF1600_StateExtractBytes(uint64_t *state, unsigned char *data,
                                   unsigned offset, unsigned length)
__contract__(
    requires(0 <= offset && offset <= KECCAK_LANES * sizeof(uint64_t) &&
	     0 <= length && length <= KECCAK_LANES * sizeof(uint64_t) - offset)
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES))
    requires(memory_no_alias(data, length))
    assigns(memory_slice(data, length))
);

#define mlk_KeccakF1600_StateXORBytes MLK_NAMESPACE(KeccakF1600_StateXORBytes)
void mlk_KeccakF1600_StateXORBytes(uint64_t *state, const unsigned char *data,
                                   unsigned offset, unsigned length)
__contract__(
    requires(0 <= offset && offset <= KECCAK_LANES * sizeof(uint64_t) &&
	     0 <= length && length <= KECCAK_LANES * sizeof(uint64_t) - offset)
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES))
    requires(memory_no_alias(data, length))
    assigns(memory_slice(state, sizeof(uint64_t) * KECCAK_LANES))
);

#define KeccakF1600x4_StateExtractBytes \
  MLK_NAMESPACE(KeccakF1600x4_StateExtractBytes)
void KeccakF1600x4_StateExtractBytes(uint64_t *state, unsigned char *data0,
                                     unsigned char *data1, unsigned char *data2,
                                     unsigned char *data3, unsigned offset,
                                     unsigned length)
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

#define mlk_KeccakF1600x4_StateXORBytes \
  MLK_NAMESPACE(KeccakF1600x4_StateXORBytes)
void mlk_KeccakF1600x4_StateXORBytes(uint64_t *state,
                                     const unsigned char *data0,
                                     const unsigned char *data1,
                                     const unsigned char *data2,
                                     const unsigned char *data3,
                                     unsigned offset, unsigned length)
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


#define mlk_KeccakF1600x4_StatePermute MLK_NAMESPACE(KeccakF1600x4_StatePermute)
void mlk_KeccakF1600x4_StatePermute(uint64_t *state)
__contract__(
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES * KECCAK_WAY))
    assigns(memory_slice(state, sizeof(uint64_t) * KECCAK_LANES * KECCAK_WAY))
);


#if !defined(MLK_USE_FIPS202_X1_ASM)
#define mlk_KeccakF1600_StatePermute MLK_NAMESPACE(KeccakF1600_StatePermute)
void mlk_KeccakF1600_StatePermute(uint64_t *state)
__contract__(
    requires(memory_no_alias(state, sizeof(uint64_t) * KECCAK_LANES))
    assigns(memory_slice(state, sizeof(uint64_t) * KECCAK_LANES))
);

#else
#define mlk_KeccakF1600_StatePermute MLK_NAMESPACE(keccak_f1600_x1_asm)
#endif

#endif /* MLK_FIPS202_KECCAKF1600_H */
