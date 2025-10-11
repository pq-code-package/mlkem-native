/* check-magic: off
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) 2025 Arm Limited
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 * check-magic: on
 */

#include "../../../../common.h"
#include "../../../../verify.h"
#include "../../api.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X4) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include <arm_mve.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>


#define KECCAK_TMP_STATE_SIZE (4 * 8 * 25)
extern void mve_keccak_state_permute_4fold_opt_m55(void *state, void *tmpstate);
int mlk_keccak_f1600_x4_native_impl(uint64_t *state)
{
  uint8_t state_4x_tmp[KECCAK_TMP_STATE_SIZE] __attribute__((aligned(16)));
  mve_keccak_state_permute_4fold_opt_m55(state, state_4x_tmp);
  mlk_zeroize(state_4x_tmp, sizeof(state_4x_tmp));
  return MLK_NATIVE_FUNC_SUCCESS;
}

extern uint32x4x2_t to_bit_interleaving_4x(uint32x4_t, uint32x4_t);
extern uint32x4x2_t from_bit_interleaving_4x(uint32x4_t, uint32x4_t);
uint32x4x2_t KeccakF1600x4_LoadBytesInLane(uint32x4_t data_ptrs,
                                           uint32_t length, uint32_t offset);
uint32x4_t KeccakF1600x4_StateXORBytes_aligned(uint32_t nvecs, uint8_t *state,
                                               uint32x4_t data_ptrs);

void KeccakF1600x4_StateXORBytes(void *state, const uint8_t *data0,
                                 const uint8_t *data1, const uint8_t *data2,
                                 const uint8_t *data3, uint32_t offset,
                                 uint32_t length)
{
  uintptr_t offset_in_lane = offset & 7;
  uintptr_t lane_offset = offset & ~7;
  uint32x4_t data_ptrs;
  __asm__ volatile(
      "vmov %q[o][2], %q[o][0], %[i0], %[i2]\n"
      "vmov %q[o][3], %q[o][1], %[i1], %[i3]\n"
      : [o] "=&w"(data_ptrs)
      : [i0] "r"(data0), [i1] "r"(data1), [i2] "r"(data2), [i3] "r"(data3)
      :);
  if (offset_in_lane)
  {
    uint32x4x2_t l;
    size_t nBytes = length < 8 - offset_in_lane ? length : 8 - offset_in_lane;

    l = KeccakF1600x4_LoadBytesInLane(data_ptrs, nBytes, offset_in_lane);

    // Now convert to bit interleaving
    uint32x4x2_t bint = to_bit_interleaving_4x(l.val[0], l.val[1]);
    uint32x4_t s0 =
        vldrwq_u32((uint32_t *)((uintptr_t)state + lane_offset / 2 * 4));
    uint32x4_t s1 =
        vldrwq_u32((uint32_t *)((uintptr_t)state + 400 + lane_offset / 2 * 4));
    s0 = veorq_u32(s0, bint.val[0]);
    s1 = veorq_u32(s1, bint.val[1]);
    vstrwq_u32((uint32_t *)((uintptr_t)state + lane_offset / 2 * 4), s0);
    vstrwq_u32((uint32_t *)((uintptr_t)state + 400 + lane_offset / 2 * 4), s1);
    length -= nBytes;
    lane_offset += 8;
    data_ptrs = vaddq_n_u32(data_ptrs, nBytes);
  }
  if (length >= 8)
  {
    uint8_t *sp0 = (uint8_t *)((uintptr_t)state + lane_offset / 2 * 4 - 16);
    uint32_t bytes_left_in_frame = 25 * 8 - lane_offset;
    uint32_t nlanes =
        (bytes_left_in_frame < length ? bytes_left_in_frame : length) / 8;

    data_ptrs = KeccakF1600x4_StateXORBytes_aligned(nlanes, sp0, data_ptrs);
    length -= nlanes * 8;
    lane_offset += nlanes * 8;
  }
  if (length)
  {
    uint32x4x2_t l;
    l = KeccakF1600x4_LoadBytesInLane(data_ptrs, length, 0);

    uint32x4x2_t bint = to_bit_interleaving_4x(l.val[0], l.val[1]);
    uint32x4_t s0 =
        vldrwq_u32((uint32_t *)((uintptr_t)state + lane_offset / 2 * 4));
    uint32x4_t s1 =
        vldrwq_u32((uint32_t *)((uintptr_t)state + 400 + lane_offset / 2 * 4));
    s0 = veorq_u32(s0, bint.val[0]);
    s1 = veorq_u32(s1, bint.val[1]);
    vstrwq_u32((uint32_t *)((uintptr_t)state + lane_offset / 2 * 4), s0);
    vstrwq_u32((uint32_t *)((uintptr_t)state + 400 + lane_offset / 2 * 4), s1);
  }
}

static inline uint32_t extract_bytes_in_lane(void *state, unsigned char *data0,
                                             unsigned char *data1,
                                             unsigned char *data2,
                                             unsigned char *data3,
                                             unsigned offset, unsigned length)
{
  // For load, need full-lane offset
  uint32_t lane_offset = offset & ~7;
  // Load the first vector.
  uint32x4_t evens =
      vldrwq_u32((uint32_t *)((uintptr_t)state + lane_offset * 2));
  uint32x4_t odds =
      vldrwq_u32((uint32_t *)((uintptr_t)state + 400 + lane_offset * 2));
  // Deinterleave
  uint32x4x2_t dint = from_bit_interleaving_4x(evens, odds);
  // Transpose the two vectors into four half-vectors
  uint32x4_t out[4];
  for (size_t i = 0; i < 4; i++)
  {
    uint32_t l = vgetq_lane_u32(dint.val[0], i);
    uint32_t h = vgetq_lane_u32(dint.val[1], i);
    out[i] = vcreateq_u32(l | ((uint64_t)h << 32), 0);
  }
  // Use predication to write the partial vector
  // Make the predicate
  uint32_t offset_in_lane = offset & 7;
  uint32_t nBytes = 8 - offset_in_lane < length ? 8 - offset_in_lane : length;
  mve_pred16_t wr_pred = ((1 << nBytes) - 1) << offset_in_lane;
  uint8x16_t ov = vidupq_n_u8(0, 1);
  vstrbq_scatter_offset_p_u8(data0 - offset_in_lane, ov, (uint8x16_t)out[0],
                             wr_pred);
  vstrbq_scatter_offset_p_u8(data1 - offset_in_lane, ov, (uint8x16_t)out[1],
                             wr_pred);
  vstrbq_scatter_offset_p_u8(data2 - offset_in_lane, ov, (uint8x16_t)out[2],
                             wr_pred);
  vstrbq_scatter_offset_p_u8(data3 - offset_in_lane, ov, (uint8x16_t)out[3],
                             wr_pred);
  return nBytes;
}

void KeccakF1600x4_StateExtract_bytes(void *state, unsigned char *data0,
                                      unsigned char *data1,
                                      unsigned char *data2,
                                      unsigned char *data3, unsigned offset,
                                      unsigned length)
{
  // Make a data pointer vector
  uint32x4_t data_addrs = vcreateq_u32(
      (uint64_t)(uintptr_t)data0 | ((uint64_t)(uintptr_t)data1 << 32),
      (uint64_t)(uintptr_t)data2 | ((uint64_t)(uintptr_t)data3 << 32));
  // Only load full 64-bit values from state
  if (offset & 7)
  {
    uint32_t nBytes = extract_bytes_in_lane(state, data0, data1, data2, data3,
                                            offset, length);
    data_addrs = vaddq_n_u32(data_addrs, nBytes);
    length -= nBytes;
    offset += nBytes;
  }
  // For each full vector
  if (length >= 8)
  {
    data_addrs = vsubq_n_u32(data_addrs, 4);
    for (; length >= 8; length -= 8)
    {
      // Load the vector & increment read pointer
      uint32x4_t evens =
          vldrwq_u32((uint32_t *)((uintptr_t)state + offset * 2));
      uint32x4_t odds =
          vldrwq_u32((uint32_t *)((uintptr_t)state + 400 + offset * 2));
      offset += 8;
      // Deinterleave
      uint32x4x2_t dint = from_bit_interleaving_4x(evens, odds);
      // Write out & increment the write pointer
      __asm__ volatile("vstrw.u32 %q[d], [%q[a], #4]!"
                       : [a] "+w"(data_addrs)
                       : [d] "w"(dint.val[0])
                       : "memory");
      __asm__ volatile("vstrw.u32 %q[d], [%q[a], #4]!"
                       : [a] "+w"(data_addrs)
                       : [d] "w"(dint.val[1])
                       : "memory");
    }
    data_addrs = vaddq_n_u32(data_addrs, 4);
  }
  if (length)
  {
    data0 = (uint8_t *)vgetq_lane_u32(data_addrs, 0);
    data1 = (uint8_t *)vgetq_lane_u32(data_addrs, 1);
    data2 = (uint8_t *)vgetq_lane_u32(data_addrs, 2);
    data3 = (uint8_t *)vgetq_lane_u32(data_addrs, 3);
    // printf("Remaining length: %u; current offset: %u\r\n", length, offset);
    extract_bytes_in_lane(state, data0, data1, data2, data3, offset, length);
  }
}
#else /* MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
MLK_EMPTY_CU(fips202_armv8_1_m_mve_keccak_4x)

#endif /* !(MLK_FIPS202_ARMV81M_NEED_X4 && !MLK_CONFIG_MULTILEVEL_NO_SHARED) \
        */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef KECCAK_TMP_STATE_SIZE
