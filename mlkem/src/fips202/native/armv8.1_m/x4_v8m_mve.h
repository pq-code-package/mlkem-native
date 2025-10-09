/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_ARMV8_1_M_X4_V8M_MVE_H
#define MLK_FIPS202_NATIVE_ARMV8_1_M_X4_V8M_MVE_H

/* Part of backend API */
#define MLK_USE_FIPS202_X1_NATIVE
#define MLK_USE_FIPS202_X1_XOR_NATIVE
#define MLK_USE_FIPS202_X4_NATIVE
#define MLK_USE_FIPS202_X4_XOR_NATIVE
/* Guard for assembly file */
#define MLK_FIPS202_ARMV81M_NEED_X1
#define MLK_FIPS202_ARMV81M_NEED_X4


#if !defined(__ASSEMBLER__)
#include <stddef.h>
#include <stdint.h>

static MLK_INLINE void mlk_zeroize(void *ptr, size_t len);

extern void KeccakF1600_StatePermute_adomnicai_m4_opt_m7(void *state);
static MLK_INLINE void mlk_keccak_f1600_x1_native(uint64_t *state)
{
  KeccakF1600_StatePermute_adomnicai_m4_opt_m7(state);
}

extern void KeccakF1600_StateXORBytes(void *state, const unsigned char *data,
                                      unsigned int offset, unsigned int length);
static MLK_INLINE void mlk_keccakf1600_xor_bytes_native(
    uint64_t *state, const unsigned char *data, unsigned offset,
    unsigned length)
{
  KeccakF1600_StateXORBytes(state, data, offset, length);
}

extern void KeccakF1600_StateExtractBytes(void *state,
                                          const unsigned char *data,
                                          unsigned int offset,
                                          unsigned int length);
static MLK_INLINE void mlk_keccakf1600_extract_bytes_native(
    uint64_t *state, const unsigned char *data, unsigned offset,
    unsigned length)
{
  KeccakF1600_StateExtractBytes(state, data, offset, length);
}

#define KECCAK_TMP_STATE_SIZE (4 * 8 * 25)
extern void mve_keccak_state_permute_4fold_opt_m55(void *state, void *tmpstate);
static MLK_INLINE void mlk_keccak_f1600_x4_native(uint64_t *state)
{
  uint8_t state_4x_tmp[KECCAK_TMP_STATE_SIZE] __attribute__((aligned(16)));
  mve_keccak_state_permute_4fold_opt_m55(state, state_4x_tmp);
  mlk_zeroize(state_4x_tmp, sizeof(state_4x_tmp));
}
void KeccakF1600x4_StateXORBytes(void *state, const uint8_t *data0,
                                 const uint8_t *data1, const uint8_t *data2,
                                 const uint8_t *data3, uint32_t offset,
                                 uint32_t length);
static MLK_INLINE void mlk_keccakf1600_xor_bytes_x4_native(
    uint64_t *state, const unsigned char *data0, const unsigned char *data1,
    const unsigned char *data2, const unsigned char *data3, unsigned offset,
    unsigned length)
{
  KeccakF1600x4_StateXORBytes(state, data0, data1, data2, data3, offset,
                              length);
}
void KeccakF1600x4_StateExtract_bytes(void *state, unsigned char *data0,
                                      unsigned char *data1,
                                      unsigned char *data2,
                                      unsigned char *data3, unsigned offset,
                                      unsigned length);
static MLK_INLINE void mlk_keccakf1600_extract_bytes_x4_native(
    uint64_t *state, unsigned char *data0, unsigned char *data1,
    unsigned char *data2, unsigned char *data3, unsigned offset,
    unsigned length)
{
  KeccakF1600x4_StateExtract_bytes(state, data0, data1, data2, data3, offset,
                                   length);
}


#endif /* !__ASSEMBLER__ */

#endif /* !MLK_FIPS202_NATIVE_ARMV8_1_M_X4_V8M_MVE_H */
