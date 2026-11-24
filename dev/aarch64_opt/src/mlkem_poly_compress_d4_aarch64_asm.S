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
  Name: poly_compress_d4_aarch64_asm
  Description: AArch64 polynomial compression (d=4)
  Signature: void mlk_poly_compress_d4_aarch64_asm(uint8_t r[128], const int16_t a[256])
  ABI:
    Architecture: aarch64
    CallingConvention: AAPCS64
    Features: [NEON]
    x0:
      type: buffer
      size_bytes: 128
      permissions: write-only
      c_parameter: uint8_t r[128]
      description: Output compressed polynomial
    x1:
      type: buffer
      size_bytes: 512
      permissions: read-only
      c_parameter: const int16_t a[256]
      description: Input polynomial
  Stack:
    bytes: 0
*/

#include "../../../common.h"
#if defined(MLK_SYS_AARCH64_NEON) && \
    defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (!defined(MLK_CONFIG_NO_ENCAPS_API) || \
     !defined(MLK_CONFIG_NO_DECAPS_API)) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)
/* simpasm: header-end */

/*
 * Compress_4 @[FIPS203, Eq (4.7)] and ByteEncode_4
 * @[FIPS203, Algorithm 5] of a polynomial.
 *
 * For u in [0, MLKEM_Q - 1], x = sqdmulh(u, 2520) = (5040 * u) >> 16 lies
 * in [0, 255], and Compress_4(u) = ((x + 8) >> 4) mod 16. After narrowing
 * x to bytes, UZP1/UZP2 separate even and odd coefficients, 8 is added to
 * both, and SRI #4 inserts bits 4..7 of the even coefficient into the low
 * nibble of the odd one. The byte addition wraps only for x >= 248, which
 * does not change the result mod 16.
 */

        in0    .req v0
        in1    .req v1
        in2    .req v2
        in3    .req v3
        in4    .req v4
        in5    .req v5
        in6    .req v6
        in7    .req v7
        q_in0  .req q0
        q_in1  .req q1
        q_in2  .req q2
        q_in3  .req q3
        q_in4  .req q4
        q_in5  .req q5
        q_in6  .req q6
        q_in7  .req q7

        lo0    .req v16
        hi0    .req v17
        lo1    .req v18
        hi1    .req v19
        even0  .req v20
        odd0   .req v21
        even1  .req v22
        odd1   .req v23

        mult   .req v24
        eight  .req v25

        dst   .req x0
        src   .req x1
        count .req x2
        wtmp  .req w3

// Compress the 8 coefficients in \x (16-bit lanes), except for the
// rounding, which is done on bytes.
.macro compress x, mult
        sqdmulh \x\().8h, \x\().8h, \mult\().8h
.endm

// From 4 vectors x0, ..., x3 of compressed coefficients (16-bit lanes),
// put the low bytes of the even coefficients into \even, and of the odd
// ones into \odd. Clobbers \lo and \hi.
.macro narrow even, odd, x0, x1, x2, x3, lo, hi
        uzp1 \lo\().16b, \x0\().16b, \x1\().16b   // bytes of x[0..15]
        uzp1 \hi\().16b, \x2\().16b, \x3\().16b   // bytes of x[16..31]
        uzp1 \even\().16b, \lo\().16b, \hi\().16b
        uzp2 \odd\().16b, \lo\().16b, \hi\().16b
.endm

// Round both and combine them: \odd = Compress_4 of the odd coefficients
// in the high nibbles, of the even coefficients in the low nibbles.
.macro pack odd, even, eight
        add \even\().16b, \even\().16b, \eight\().16b
        add \odd\().16b, \odd\().16b, \eight\().16b
        sri \odd\().16b, \even\().16b, #4
.endm

        .text
        .global MLK_ASM_NAMESPACE(poly_compress_d4_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d4_aarch64_asm)

        mov  wtmp, #2520 // 2 * round(2^22 / MLKEM_Q)
        dup  mult.8h, wtmp
        movi eight.16b, #8

        // Each iteration compresses 64 coefficients into 32 bytes
        mov count, #4
mlk_poly_compress_d4_loop_start:
        ldp q_in0, q_in1, [src], #128
        ldp q_in2, q_in3, [src, #-96]
        ldp q_in4, q_in5, [src, #-64]
        ldp q_in6, q_in7, [src, #-32]

        compress in0, mult
        compress in1, mult
        compress in2, mult
        compress in3, mult
        compress in4, mult
        compress in5, mult
        compress in6, mult
        compress in7, mult

        narrow even0, odd0, in0, in1, in2, in3, lo0, hi0
        narrow even1, odd1, in4, in5, in6, in7, lo1, hi1

        pack odd0, even0, eight
        pack odd1, even1, eight

        st1 {odd0.16b}, [dst], #16
        st1 {odd1.16b}, [dst], #16

        subs count, count, #1
        cbnz count, mlk_poly_compress_d4_loop_start
        ret

        .unreq in0
        .unreq in1
        .unreq in2
        .unreq in3
        .unreq in4
        .unreq in5
        .unreq in6
        .unreq in7
        .unreq q_in0
        .unreq q_in1
        .unreq q_in2
        .unreq q_in3
        .unreq q_in4
        .unreq q_in5
        .unreq q_in6
        .unreq q_in7
        .unreq lo0
        .unreq hi0
        .unreq lo1
        .unreq hi1
        .unreq even0
        .unreq odd0
        .unreq even1
        .unreq odd1
        .unreq mult
        .unreq eight
        .unreq dst
        .unreq src
        .unreq count
        .unreq wtmp

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && (!MLK_CONFIG_NO_ENCAPS_API || \
          !MLK_CONFIG_NO_DECAPS_API) && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || \
          MLKEM_K == 2 || MLKEM_K == 3) */
