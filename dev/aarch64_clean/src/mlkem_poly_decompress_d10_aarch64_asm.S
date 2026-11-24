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
  Name: poly_decompress_d10_aarch64_asm
  Description: Decompression of a polynomial from 10 bits per coefficient
  Signature: void mlk_poly_decompress_d10_aarch64_asm(int16_t r[256], const uint8_t a[320], const uint8_t table[80])
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
      size_bytes: 320
      permissions: read-only
      c_parameter: const uint8_t a[320]
      description: Input compressed polynomial
    x2:
      type: buffer
      size_bytes: 80
      permissions: read-only
      c_parameter: const uint8_t table[80]
      description: Constants (index, shift, mask and multiplier vectors)
  Stack:
    bytes: 0
*/

#include "../../../common.h"
#if defined(MLK_SYS_AARCH64_NEON) && \
    defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    !defined(MLK_CONFIG_NO_DECAPS_API) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)
/* simpasm: header-end */

/*
 * ByteDecode_10 @[FIPS203, Algorithm 6] and Decompress_10
 * @[FIPS203, Eq (4.8)] of a polynomial.
 *
 * Every 5 bytes hold 4 coefficients. Coefficient 4g + k (k = 0, 1, 2, 3)
 * occupies bits 2k .. 2k + 9 of bytes 5g + k and 5g + k + 1. For each 8
 * coefficients,
 *
 * - TBL copies these two bytes into 16-bit lane 4g + k,
 * - USHL by 2 - 2k (a negative count shifts right) moves the coefficient
 *   to bits 2..11, and AND with 0x3ff << 2 clears all other bits,
 * - SQRDMULH by MLKEM_Q << 3 computes
 *     (2 * (x << 2) * (MLKEM_Q << 3) + 2^15) >> 16
 *       = (x * MLKEM_Q + 512) >> 10 = Decompress_10(x).
 *
 * An iteration handles 40 bytes. To not read past the input, the last 10
 * bytes are taken from a 16-byte load at byte 24, using indices shifted
 * by 6.
 *
 * The table (x2) holds the index, shift, mask and multiplier vectors, see
 * mlk_aarch64_decompress_d10_table.
 */

.macro unpack dst, src, idx, shifts, mask
        tbl  \dst\().16b, {\src\().16b}, \idx\().16b
        ushl \dst\().8h, \dst\().8h, \shifts\().8h
        and  \dst\().16b, \dst\().16b, \mask\().16b
.endm

.macro decompress dst, mult
        sqrdmulh \dst\().8h, \dst\().8h, \mult\().8h
.endm

        dst      .req x0
        src      .req x1
        table    .req x2
        count    .req x3
        src1     .req x4
        src2     .req x5
        src3     .req x6

        in0      .req v0
        in1      .req v1
        in2      .req v2
        in3      .req v3
        out0     .req v4
        out1     .req v5
        out2     .req v6
        out3     .req v7
        q_out0   .req q4
        q_out1   .req q5
        q_out2   .req q6
        q_out3   .req q7

        idx0     .req v16 // idx0, idx6, shifts, mask must be consecutive
        idx6     .req v17 // for LD1
        shifts   .req v18
        mask     .req v19
        mult     .req v20

        .text
        .global MLK_ASM_NAMESPACE(poly_decompress_d10_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d10_aarch64_asm)

        // idx0 = [0,1, 1,2, 2,3, 3,4, 5,6, 6,7, 7,8, 8,9], idx6 = idx0 + 6,
        // shifts = [2, 0, -2, -4, 2, 0, -2, -4], mask = 0x3ff << 2
        ld1 {idx0.16b, idx6.16b, shifts.16b, mask.16b}, [table], #64
        // mult = MLKEM_Q << 3
        ld1 {mult.16b}, [table]

        // Each iteration decompresses 40 bytes into 32 coefficients.
        mov count, #8
mlk_poly_decompress_d10_loop_start:
        // Bytes 0-9, 10-19, 20-29 at offset 0 of in0, in1, in2,
        // and bytes 30-39 at offset 6 of in3.
        add src1, src, #10
        add src2, src, #20
        add src3, src, #24
        ld1 {in0.16b}, [src]
        ld1 {in1.16b}, [src1]
        ld1 {in2.16b}, [src2]
        ld1 {in3.16b}, [src3]
        add src, src, #40

        unpack out0, in0, idx0, shifts, mask
        unpack out1, in1, idx0, shifts, mask
        unpack out2, in2, idx0, shifts, mask
        unpack out3, in3, idx6, shifts, mask

        decompress out0, mult
        decompress out1, mult
        decompress out2, mult
        decompress out3, mult

        stp q_out0, q_out1, [dst], #64
        stp q_out2, q_out3, [dst, #-32]

        subs count, count, #1
        cbnz count, mlk_poly_decompress_d10_loop_start
        ret

        .unreq dst
        .unreq src
        .unreq table
        .unreq src1
        .unreq src2
        .unreq src3
        .unreq count
        .unreq in0
        .unreq in1
        .unreq in2
        .unreq in3
        .unreq out0
        .unreq out1
        .unreq out2
        .unreq out3
        .unreq q_out0
        .unreq q_out1
        .unreq q_out2
        .unreq q_out3
        .unreq idx0
        .unreq idx6
        .unreq shifts
        .unreq mask
        .unreq mult

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && !MLK_CONFIG_NO_DECAPS_API && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == 3) \
        */
