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
  Name: poly_decompress_d11_aarch64_asm
  Description: Decompression of a polynomial from 11 bits per coefficient
  Signature: void mlk_poly_decompress_d11_aarch64_asm(int16_t r[256], const uint8_t a[352], const uint8_t table[112])
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
      size_bytes: 352
      permissions: read-only
      c_parameter: const uint8_t a[352]
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
 * ByteDecode_11 @[FIPS203, Algorithm 6] and Decompress_11
 * @[FIPS203, Eq (4.8)] of a polynomial.
 *
 * Every 11 bytes hold 8 coefficients. Coefficient k starts at bit
 * o_k = 11k mod 8 of byte b_k = floor(11k / 8):
 *
 *   k   |  0  1  2  3  4  5  6  7
 *   b_k |  0  1  2  4  5  6  8  9
 *   o_k |  0  3  6  1  4  7  2  5
 *
 * For each group of 8 coefficients,
 *
 * - TBL (idx_lo) copies bytes b_k and b_k + 1 into 16-bit lane k, and USHL
 *   (a negative count shifts right) moves bit o_k to bit A_k, where
 *   A_k = 1 except A_2 = 2 and A_5 = 3,
 * - coefficients 2 and 5 extend into byte b_k + 2: TBL (idx_hi) copies
 *   that byte into the low byte of the lane, and SLI #12 inserts its low
 *   bits at bits 12..15,
 * - AND with 0x7ff << A_k clears all other bits, leaving x << A_k,
 * - SQRDMULH by MLKEM_Q << (4 - A_k) computes
 *     (2 * (x << A_k) * (MLKEM_Q << (4 - A_k)) + 2^15) >> 16
 *       = (x * MLKEM_Q + 2^10) >> 11 = Decompress_11(x).
 *
 * An iteration handles 44 bytes. To not read past the input, the last 11
 * bytes are taken from a 16-byte load at byte 28, using indices shifted
 * by 5. The out-of-range indices 16 and 17 this creates in idx_hi occur
 * only in lanes other than 2 and 5, where the AND clears bits 12..15.
 *
 * The table (x2) holds the index, shift, mask and multiplier vectors, see
 * mlk_aarch64_decompress_d11_table.
 */

.macro unpack dst, src, idx_lo, idx_hi, shifts, mask, tmp
        tbl  \dst\().16b, {\src\().16b}, \idx_lo\().16b
        tbl  \tmp\().16b, {\src\().16b}, \idx_hi\().16b
        ushl \dst\().8h, \dst\().8h, \shifts\().8h
        sli  \dst\().8h, \tmp\().8h, #12
        and  \dst\().16b, \dst\().16b, \mask\().16b
.endm

.macro decompress dst, mult
        sqrdmulh \dst\().8h, \dst\().8h, \mult\().8h
.endm

        dst       .req x0
        src       .req x1
        table     .req x2
        count     .req x3
        src1      .req x4
        src2      .req x5
        src3      .req x6

        in0       .req v0
        in1       .req v1
        in2       .req v2
        in3       .req v3
        out0      .req v4
        out1      .req v5
        out2      .req v6
        out3      .req v7
        q_out0    .req q4
        q_out1    .req q5
        q_out2    .req q6
        q_out3    .req q7
        t0        .req v16
        t1        .req v17
        t2        .req v18
        t3        .req v19

        idx_lo    .req v24 // idx_lo, idx_hi, idx_lo5, idx_hi5 must be
        idx_hi    .req v25 // consecutive for LD1
        idx_lo5   .req v26
        idx_hi5   .req v27
        shifts    .req v28 // shifts and mask must be consecutive for LD1
        mask      .req v29
        mult      .req v30

        .text
        .global MLK_ASM_NAMESPACE(poly_decompress_d11_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d11_aarch64_asm)

        // idx_lo = [0,1, 1,2, 2,3, 4,5, 5,6, 6,7, 8,9, 9,10],
        // idx_hi = idx_lo + 2, idx_lo5 = idx_lo + 5, idx_hi5 = idx_hi + 5
        ld1 {idx_lo.16b, idx_hi.16b, idx_lo5.16b, idx_hi5.16b}, [table], #64
        // shifts = [1, -2, -4, 0, -3, -4, -1, -4],
        // mask = 0x7ff << A_k with A = [1, 1, 2, 1, 1, 3, 1, 1]
        ld1 {shifts.16b, mask.16b}, [table], #32
        // mult = 3329 << (4 - A_k) = [26632, 26632, 13316, 26632,
        //                             26632, 6658, 26632, 26632]
        ld1 {mult.16b}, [table]

        // Each iteration decompresses 44 bytes into 32 coefficients.
        mov count, #8
mlk_poly_decompress_d11_loop_start:
        // Bytes 0-10, 11-21, 22-32 at offset 0 of in0, in1, in2,
        // and bytes 33-43 at offset 5 of in3.
        add src1, src, #11
        add src2, src, #22
        add src3, src, #28
        ld1 {in0.16b}, [src]
        ld1 {in1.16b}, [src1]
        ld1 {in2.16b}, [src2]
        ld1 {in3.16b}, [src3]
        add src, src, #44

        unpack out0, in0, idx_lo, idx_hi, shifts, mask, t0
        unpack out1, in1, idx_lo, idx_hi, shifts, mask, t1
        unpack out2, in2, idx_lo, idx_hi, shifts, mask, t2
        unpack out3, in3, idx_lo5, idx_hi5, shifts, mask, t3

        decompress out0, mult
        decompress out1, mult
        decompress out2, mult
        decompress out3, mult

        stp q_out0, q_out1, [dst], #64
        stp q_out2, q_out3, [dst, #-32]

        subs count, count, #1
        cbnz count, mlk_poly_decompress_d11_loop_start
        ret

        .unreq dst
        .unreq src
        .unreq table
        .unreq count
        .unreq src1
        .unreq src2
        .unreq src3
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
        .unreq t0
        .unreq t1
        .unreq t2
        .unreq t3
        .unreq idx_lo
        .unreq idx_hi
        .unreq idx_lo5
        .unreq idx_hi5
        .unreq shifts
        .unreq mask
        .unreq mult

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && !MLK_CONFIG_NO_DECAPS_API && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
