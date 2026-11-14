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
  Name: poly_decompress_d4_aarch64_asm
  Description: Decompression of a polynomial from 4 bits per coefficient
  Signature: void mlk_poly_decompress_d4_aarch64_asm(int16_t r[256], const uint8_t a[128], const uint8_t table[32])
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
      size_bytes: 128
      permissions: read-only
      c_parameter: const uint8_t a[128]
      description: Input compressed polynomial
    x2:
      type: buffer
      size_bytes: 32
      permissions: read-only
      c_parameter: const uint8_t table[32]
      description: Lookup table for Decompress_4
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
 * ByteDecode_4 @[FIPS203, Algorithm 6] and Decompress_4
 * @[FIPS203, Eq (4.8)] of a polynomial.
 *
 * AND and USHR split each input byte into its low (even) and high (odd)
 * nibble, and ZIP1/ZIP2 restore coefficient order. A 4-bit value has only
 * 16 values, so two TBL lookups give the low and high bytes of
 * Decompress_4(x) = (x * MLKEM_Q + 8) >> 4, which ST2 interleaves into
 * 16-bit coefficients.
 *
 * The table (x2) holds the 16 low bytes followed by the 16 high bytes,
 * see mlk_aarch64_decompress_d4_table.
 */

        dst      .req x0
        src      .req x1
        table    .req x2
        count    .req x3

        in       .req v0
        lo       .req v1
        hi       .req v2
        coeffs0  .req v3
        coeffs1  .req v16
        lob0     .req v4  // lob0 and hib0 must be consecutive for ST2
        hib0     .req v5
        lob1     .req v6  // lob1 and hib1 must be consecutive for ST2
        hib1     .req v7
        tlo      .req v17 // tlo and thi must be consecutive for LD1
        thi      .req v18
        mask     .req v19

// Split the 16 input bytes in \in into their 32 nibbles, in coefficient
// order: \c0 holds coefficients 0..15, \c1 coefficients 16..31.
.macro unpack c0, c1, in
        and  lo.16b, \in\().16b, mask.16b
        ushr hi.16b, \in\().16b, #4
        zip1 \c0\().16b, lo.16b, hi.16b
        zip2 \c1\().16b, lo.16b, hi.16b
.endm

// Look up the low and high bytes of Decompress_4 for the 16 nibbles in \c.
.macro decompress lob, hib, c
        tbl  \lob\().16b, {tlo.16b}, \c\().16b
        tbl  \hib\().16b, {thi.16b}, \c\().16b
.endm

        .text
        .global MLK_ASM_NAMESPACE(poly_decompress_d4_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_decompress_d4_aarch64_asm)

        ld1  {tlo.16b, thi.16b}, [table]
        movi mask.16b, #0x0f

        // Each iteration decompresses 16 bytes into 32 coefficients.
        mov count, #8
mlk_poly_decompress_d4_loop_start:
        ld1  {in.16b}, [src], #16

        unpack     coeffs0, coeffs1, in
        decompress lob0, hib0, coeffs0
        decompress lob1, hib1, coeffs1

        st2  {lob0.16b, hib0.16b}, [dst], #32
        st2  {lob1.16b, hib1.16b}, [dst], #32

        subs count, count, #1
        cbnz count, mlk_poly_decompress_d4_loop_start
        ret

        .unreq dst
        .unreq src
        .unreq table
        .unreq count
        .unreq in
        .unreq lo
        .unreq hi
        .unreq coeffs0
        .unreq coeffs1
        .unreq lob0
        .unreq hib0
        .unreq lob1
        .unreq hib1
        .unreq tlo
        .unreq thi
        .unreq mask

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && !MLK_CONFIG_NO_DECAPS_API && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == 3) \
        */
