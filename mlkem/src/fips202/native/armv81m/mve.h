/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_ARMV81M_MVE_H
#define MLK_FIPS202_NATIVE_ARMV81M_MVE_H

#define MLK_FIPS202_NATIVE_ARMV81M

/* Part of backend API */
#define MLK_USE_FIPS202_X4_NATIVE
#define MLK_USE_FIPS202_X4_XOR_BYTES_NATIVE
#define MLK_USE_FIPS202_X4_EXTRACT_BYTES_NATIVE
/* Guard for assembly file */
#define MLK_FIPS202_ARMV81M_NEED_X4

#if !defined(__ASSEMBLER__)
#include "../api.h"
#include "src/fips202_native_armv81m.h"

#define MLK_KECCAKF1600_X4_BITINTERLEAVED_ODD_WORDS 50u

/*
 * Native x4 permutation
 * State is kept in bit-interleaved format.
 */
#define mlk_keccak_f1600_x4_native_impl \
  MLK_NAMESPACE(keccak_f1600_x4_native_impl)
int mlk_keccak_f1600_x4_native_impl(uint64_t *state);

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_keccak_f1600_x4_native(uint64_t *state)
{
  return mlk_keccak_f1600_x4_native_impl(state);
}

/*
 * Slow path for buffers that the MVE word gather/scatter main loops cannot
 * access directly. Returning MLK_NATIVE_FUNC_FALLBACK is not safe here because
 * the Armv8.1-M x4 state is bit-interleaved, while the generic C x4 fallback
 * uses four contiguous scalar Keccak states.
 */
static MLK_INLINE uint32_t mlk_keccakf1600x4_bitinterleave_even_u8(uint8_t x)
{
  uint32_t r;

  r = x & 0x01u;
  r |= (x & 0x04u) >> 1;
  r |= (x & 0x10u) >> 2;
  r |= (x & 0x40u) >> 3;
  return r;
}

static MLK_INLINE uint32_t mlk_keccakf1600x4_bitinterleave_odd_u8(uint8_t x)
{
  uint32_t r;

  r = (x & 0x02u) >> 1;
  r |= (x & 0x08u) >> 2;
  r |= (x & 0x20u) >> 3;
  r |= (x & 0x80u) >> 4;
  return r;
}

static MLK_INLINE uint8_t mlk_keccakf1600x4_bitdeinterleave_u8(uint32_t even,
                                                               uint32_t odd)
{
  uint8_t r;

  r = (uint8_t)(even & 0x01u);
  r = (uint8_t)(r | ((odd & 0x01u) << 1));
  r = (uint8_t)(r | ((even & 0x02u) << 1));
  r = (uint8_t)(r | ((odd & 0x02u) << 2));
  r = (uint8_t)(r | ((even & 0x04u) << 2));
  r = (uint8_t)(r | ((odd & 0x04u) << 3));
  r = (uint8_t)(r | ((even & 0x08u) << 3));
  r = (uint8_t)(r | ((odd & 0x08u) << 4));
  return r;
}

static MLK_INLINE void mlk_keccakf1600x4_xor_bitinterleaved_byte(
    uint64_t *state, uint8_t data, unsigned byte_offset, unsigned instance)
{
  unsigned lane;
  unsigned byte_in_lane;
  unsigned state_index;
  unsigned shift;
  uint64_t even;
  uint64_t odd;

  lane = byte_offset >> 3;
  byte_in_lane = byte_offset & 7u;
  state_index = (2u * lane) + (instance >> 1);
  shift = 32u * (instance & 1u);

  even = (uint64_t)mlk_keccakf1600x4_bitinterleave_even_u8(data)
         << (4u * byte_in_lane);
  odd = (uint64_t)mlk_keccakf1600x4_bitinterleave_odd_u8(data)
        << (4u * byte_in_lane);

  state[state_index] ^= even << shift;
  state[MLK_KECCAKF1600_X4_BITINTERLEAVED_ODD_WORDS + state_index] ^= odd
                                                                      << shift;
}

static MLK_INLINE uint8_t mlk_keccakf1600x4_extract_bitinterleaved_byte(
    uint64_t *state, unsigned byte_offset, unsigned instance)
{
  unsigned lane;
  unsigned byte_in_lane;
  unsigned state_index;
  unsigned shift;
  uint32_t even;
  uint32_t odd;

  lane = byte_offset >> 3;
  byte_in_lane = byte_offset & 7u;
  state_index = (2u * lane) + (instance >> 1);
  shift = 32u * (instance & 1u);

  even =
      (uint32_t)((state[state_index] >> shift) >> (4u * byte_in_lane)) & 0x0Fu;
  odd = (uint32_t)((state[MLK_KECCAKF1600_X4_BITINTERLEAVED_ODD_WORDS +
                          state_index] >>
                    shift) >>
                   (4u * byte_in_lane)) &
        0x0Fu;

  return mlk_keccakf1600x4_bitdeinterleave_u8(even, odd);
}

static MLK_INLINE void mlk_keccakf1600_xor_bytes_x4_bitinterleaved_c(
    uint64_t *state, const uint8_t *data0, const uint8_t *data1,
    const uint8_t *data2, const uint8_t *data3, unsigned offset,
    unsigned length)
{
  unsigned i;

  for (i = 0; i < length; i++)
  {
    unsigned byte_offset;

    byte_offset = offset + i;
    mlk_keccakf1600x4_xor_bitinterleaved_byte(state, data0[i], byte_offset, 0);
    mlk_keccakf1600x4_xor_bitinterleaved_byte(state, data1[i], byte_offset, 1);
    mlk_keccakf1600x4_xor_bitinterleaved_byte(state, data2[i], byte_offset, 2);
    mlk_keccakf1600x4_xor_bitinterleaved_byte(state, data3[i], byte_offset, 3);
  }
}

static MLK_INLINE void mlk_keccakf1600_extract_bytes_x4_bitinterleaved_c(
    uint64_t *state, uint8_t *data0, uint8_t *data1, uint8_t *data2,
    uint8_t *data3, unsigned offset, unsigned length)
{
  unsigned i;

  for (i = 0; i < length; i++)
  {
    unsigned byte_offset;

    byte_offset = offset + i;
    data0[i] =
        mlk_keccakf1600x4_extract_bitinterleaved_byte(state, byte_offset, 0);
    data1[i] =
        mlk_keccakf1600x4_extract_bitinterleaved_byte(state, byte_offset, 1);
    data2[i] =
        mlk_keccakf1600x4_extract_bitinterleaved_byte(state, byte_offset, 2);
    data3[i] =
        mlk_keccakf1600x4_extract_bitinterleaved_byte(state, byte_offset, 3);
  }
}

/*
 * Native x4 XOR bytes (with on-the-fly bit interleaving)
 */
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_keccakf1600_xor_bytes_x4_native(
    uint64_t *state, const uint8_t *data0, const uint8_t *data1,
    const uint8_t *data2, const uint8_t *data3, unsigned offset,
    unsigned length)
{
  unsigned offset_mod8;
  unsigned byte_prefix;
  unsigned main_length;

  offset_mod8 = offset & 7u;
  byte_prefix = 0;
  if (offset_mod8 != 0u)
  {
    byte_prefix = 8u - offset_mod8;
    if (byte_prefix > length)
    {
      byte_prefix = length;
    }
  }

  main_length = length - byte_prefix;
  if (main_length >= 8u &&
      ((((uintptr_t)data0 + byte_prefix) | ((uintptr_t)data1 + byte_prefix) |
        ((uintptr_t)data2 + byte_prefix) | ((uintptr_t)data3 + byte_prefix)) &
       3u) != 0u)
  {
    mlk_keccakf1600_xor_bytes_x4_bitinterleaved_c(state, data0, data1, data2,
                                                  data3, offset, length);
    return MLK_NATIVE_FUNC_SUCCESS;
  }

  mlk_keccak_f1600_x4_state_xor_bytes_asm(state, data0, data1, data2, data3,
                                          offset, length);
  return MLK_NATIVE_FUNC_SUCCESS;
}

/*
 * Native x4 extract bytes (with on-the-fly bit de-interleaving)
 */
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_keccakf1600_extract_bytes_x4_native(
    uint64_t *state, uint8_t *data0, uint8_t *data1, uint8_t *data2,
    uint8_t *data3, unsigned offset, unsigned length)
{
  unsigned offset_mod8;
  unsigned byte_prefix;
  unsigned main_length;

  offset_mod8 = offset & 7u;
  byte_prefix = 0;
  if (offset_mod8 != 0u)
  {
    byte_prefix = 8u - offset_mod8;
    if (byte_prefix > length)
    {
      byte_prefix = length;
    }
  }

  main_length = length - byte_prefix;
  if (main_length >= 8u &&
      ((((uintptr_t)data0 + byte_prefix) | ((uintptr_t)data1 + byte_prefix) |
        ((uintptr_t)data2 + byte_prefix) | ((uintptr_t)data3 + byte_prefix)) &
       3u) != 0u)
  {
    mlk_keccakf1600_extract_bytes_x4_bitinterleaved_c(
        state, data0, data1, data2, data3, offset, length);
    return MLK_NATIVE_FUNC_SUCCESS;
  }

  mlk_keccak_f1600_x4_state_extract_bytes_asm(state, data0, data1, data2, data3,
                                              offset, length);
  return MLK_NATIVE_FUNC_SUCCESS;
}

#endif /* !__ASSEMBLER__ */

#undef MLK_KECCAKF1600_X4_BITINTERLEAVED_ODD_WORDS

#endif /* !MLK_FIPS202_NATIVE_ARMV81M_MVE_H */
