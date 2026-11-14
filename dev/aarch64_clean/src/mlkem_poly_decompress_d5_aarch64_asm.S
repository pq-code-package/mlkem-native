/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS203]
 *   FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/203/final
 */

/*yaml
  Name: poly_decompress_d5_aarch64_asm
  Description: Decompression of a polynomial from 5 bits per coefficient
  Signature: void mlk_poly_decompress_d5_aarch64_asm(int16_t r[256], const uint8_t a[160], const uint8_t table[112])
  ABI:
    Architecture: aarch64
    CallingConvention: AAPCS64
    Features: [NEON]
    x0:
      type: buffer
      size_bytes: 512
      permissions: write-only
      c_parameter: int16_t r[256]
      description: Output polynomial
    x1:
      type: buffer
      size_bytes: 160
      permissions: read-only
      c_parameter: const uint8_t a[160]
      description: Input compressed polynomial
    x2:
      type: buffer
      size_bytes: 112
      permissions: read-only
      c_parameter: const uint8_t table[112]
      description: Constants (index, shift, mask and multiplier vectors)
  Stack:
    bytes: 0
*/

#include "../../../common.h"
#if defined(MLK_SYS_AARCH64_NEON) && \
    defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    !defined(MLK_CONFIG_NO_DECAPS_API) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)
/* simpasm: header-end */

/*
 * ByteDecode_5 @[FIPS203, Algorithm 6] and Decompress_5
 * @[FIPS203, Eq (4.8)] of a polynomial.
 *
 * Every 5 bytes hold 8 coefficients. Coefficient j starts at bit
 * s_j = 5j mod 8 of byte b_j = floor(5j / 8) and lies within bytes b_j and
 * b_j + 1. For each group of 8 coefficients,
 *
 * - TBL copies bytes b_j and b_j + 1 into 16-bit lane j,
 * - USHL by 7 - s_j moves the coefficient to bits 7..11, and AND with
 *   0x1f << 7 clears all other bits,
 * - SQRDMULH by MLKEM_Q << 3 computes
 *     (2 * (x << 7) * (MLKEM_Q << 3) + 2^15) >> 16
 *       = (x * MLKEM_Q + 16) >> 5 = Decompress_5(x).
 *
 * An iteration handles 20 bytes, that is, 4 groups starting at bytes 0, 5,
 * 10 and 15. To not read past the input, the last group is taken from a
 * second 16-byte load at byte 4, where it starts at offset 11. The index
 * of the upper byte of lane 7 then becomes 16, for which TBL returns 0;
 * that byte is not needed.
 *
 * The table (x2) holds the index, shift, mask and multiplier vectors, see
 * mlk_aarch64_decompress_d5_table.
 */

.macro unpack dst, src, idx, shifts, mask
        tbl  \dst\().16b, {\src\().16b}, \idx\().16b
        ushl \dst\().8h, \dst\().8h, \shifts\().8h
        and  \dst\().16b, \dst\().16b, \mask\().16b
.endm

.macro decompress dst, mult
        sqrdmulh \dst\().8h, \dst\().8h, \mult\().8h
.endm

        dst     .req x0
        src     .req x1
        table   .req x2
        count   .req x3
        src1    .req x4

        in0     .req v0
        in1     .req v1
        out0    .req v2
        q_out0  .req q2
        out1    .req v3
        q_out1  .req q3
        out2    .req v4
        q_out2  .req q4
        out3    .req v5
        q_out3  .req q5

        idx0    .req v16 // idx0, idx5, idx10, idx11 must be consecutive
        idx5    .req v17 // for LD1
        idx10   .req v18
        idx11   .req v19
        shifts  .req v20 // shifts and mask must be consecutive for LD1
        mask    .req v21
        mult    .req v22

        .text
        .global MLK_ASM_NAMESPACE(poly_decompress_d5_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d5_aarch64_asm)

        // idx0: lane j (as 16-bit lanes) holds bytes b_j and b_j + 1,
        // i.e. the 16-bit value 0x0101 * b_j + 0x0100. idx5, idx10, idx11:
        // the same for groups starting at bytes 5, 10 and 11.
        ld1 {idx0.16b, idx5.16b, idx10.16b, idx11.16b}, [table], #64
        // shifts: lane j holds 7 - s_j = 7, 2, 5, 0, 3, 6, 1, 4.
        // mask: 0x1f << 7 in each lane.
        ld1 {shifts.16b, mask.16b}, [table], #32
        // mult: 3329 << 3 in each lane.
        ld1 {mult.16b}, [table]

        // Each iteration decompresses 20 bytes into 32 coefficients.
        mov count, #8
mlk_poly_decompress_d5_loop_start:
        add src1, src, #4
        ld1 {in0.16b}, [src]
        ld1 {in1.16b}, [src1]
        add src, src, #20

        unpack out0, in0, idx0, shifts, mask
        unpack out1, in0, idx5, shifts, mask
        unpack out2, in0, idx10, shifts, mask
        unpack out3, in1, idx11, shifts, mask

        decompress out0, mult
        decompress out1, mult
        decompress out2, mult
        decompress out3, mult

        stp q_out0, q_out1, [dst], #64
        stp q_out2, q_out3, [dst, #-32]

        subs count, count, #1
        cbnz count, mlk_poly_decompress_d5_loop_start
        ret

        .unreq dst
        .unreq src
        .unreq table
        .unreq count
        .unreq src1
        .unreq in0
        .unreq in1
        .unreq out0
        .unreq q_out0
        .unreq out1
        .unreq q_out1
        .unreq out2
        .unreq q_out2
        .unreq out3
        .unreq q_out3
        .unreq idx0
        .unreq idx5
        .unreq idx10
        .unreq idx11
        .unreq shifts
        .unreq mask
        .unreq mult

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && !MLK_CONFIG_NO_DECAPS_API && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
