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
  Name: poly_compress_d11_aarch64_asm
  Description: AArch64 polynomial compression (d=11)
  Signature: void mlk_poly_compress_d11_aarch64_asm(uint8_t r[352], const int16_t a[256])
  ABI:
    Architecture: aarch64
    CallingConvention: AAPCS64
    Features: [NEON]
    x0:
      type: buffer
      size_bytes: 352
      permissions: write-only
      c_parameter: uint8_t r[352]
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
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)
/* simpasm: header-end */

/*
 * Compress_11 @[FIPS203, Eq (4.7)] and ByteEncode_11
 * @[FIPS203, Algorithm 5] of a polynomial.
 *
 * For u in [0, MLKEM_Q - 1], Compress_11(u) = sqrdmulh(u, 1321131424) on
 * 32-bit lanes, where 1321131424 = round(2^42 / MLKEM_Q). The result is
 * at most 2047, so no reduction is needed.
 *
 * LD2 on 64-bit elements loads 16 coefficients such that one vector holds
 * the first 4 coefficients of two groups of 8, and the other vector the
 * last 4. As for d = 10, TRN1/TRN2 and two levels of SLI pack 4
 * coefficients into the low 44 bits of each 64-bit lane; pack_cross then
 * puts the 11 bytes of each group into bytes 0..10 of a vector.
 *
 * Each group is written by a 16-byte store whose last 5 bytes are
 * overwritten by the next store, so the stores must stay in increasing
 * address order. To not write past the end of an 88-byte block, the last
 * group is written by two 8-byte stores.
 */

        in0    .req v0
        in1    .req v1
        in2    .req v2
        in3    .req v3
        in4    .req v4
        in5    .req v5
        in6    .req v6
        in7    .req v7

        t0     .req v16
        out0   .req v17
        out1   .req v18
        out2   .req v19
        out3   .req v20
        out4   .req v21
        out5   .req v22
        out6   .req v23
        out7   .req v26
        last   .req v27

        zero   .req v24
        mult   .req v25

        dst    .req x0
        src    .req x1
        xtmp   .req x3
        wtmp   .req w3

// x[0], ..., x[7] -> even coefficients in the 32-bit lanes of x, odd ones in
// the 32-bit lanes of t; y = sqrdmulh(u, M) with M = round(2^42 / MLKEM_Q)
.macro compress x, t
        trn2     \t\().8h, \x\().8h, zero.8h
        trn1     \x\().8h, \x\().8h, zero.8h
        sqrdmulh \x\().4s, \x\().4s, mult.4s
        sqrdmulh \t\().4s, \t\().4s, mult.4s
.endm

// p[i] = (y[2i] mod 2^11) | y[2i+1] << 11 in the 32-bit lanes of x,
// then g[i] = (p[2i] mod 2^22) | p[2i+1] << 22 in the 64-bit lanes of x
.macro pack x, t
        sli  \x\().4s, \t\().4s, #11
        trn2 \t\().4s, \x\().4s, zero.4s
        sli  \x\().2d, \t\().2d, #22
.endm

// x = (g0, h0), y = (g1, h1) -> o0[0..10] = g0 | g1 << 44,
// o1[0..10] = h0 | h1 << 44
.macro pack_cross x, y, o0, o1
        sli  \x\().2d, \y\().2d, #44
        ushr \y\().2d, \y\().2d, #20
        zip1 \o0\().2d, \x\().2d, \y\().2d
        zip2 \o1\().2d, \x\().2d, \y\().2d
.endm

// Compress the 64 coefficients at src into 88 bytes at dst;
// src advances by 128, dst by 88
.macro block
        ld2 {in0.2d, in1.2d}, [src], #32
        ld2 {in2.2d, in3.2d}, [src], #32
        ld2 {in4.2d, in5.2d}, [src], #32
        ld2 {in6.2d, in7.2d}, [src], #32

        compress   in0, t0
        pack       in0, t0
        compress   in1, t0
        pack       in1, t0
        pack_cross in0, in1, out0, out1

        compress   in2, t0
        pack       in2, t0
        compress   in3, t0
        pack       in3, t0
        pack_cross in2, in3, out2, out3

        compress   in4, t0
        pack       in4, t0
        compress   in5, t0
        pack       in5, t0
        pack_cross in4, in5, out4, out5

        compress   in6, t0
        pack       in6, t0
        compress   in7, t0
        pack       in7, t0
        pack_cross in6, in7, out6, out7

        // bytes 3..10 of the last group
        ext  last.16b, out7.16b, out7.16b, #3

        st1 {out0.16b}, [dst], #16
        sub dst, dst, #5
        st1 {out1.16b}, [dst], #16
        sub dst, dst, #5
        st1 {out2.16b}, [dst], #16
        sub dst, dst, #5
        st1 {out3.16b}, [dst], #16
        sub dst, dst, #5
        st1 {out4.16b}, [dst], #16
        sub dst, dst, #5
        st1 {out5.16b}, [dst], #16
        sub dst, dst, #5
        st1 {out6.16b}, [dst], #16
        sub dst, dst, #5
        st1 {out7.8b}, [dst], #8
        sub dst, dst, #5
        st1 {last.8b}, [dst], #8
.endm

        .text
        .global MLK_ASM_NAMESPACE(poly_compress_d11_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d11_aarch64_asm)

mlk_poly_compress_d11_start:
        movi zero.2d, #0

        mov  xtmp, #0xdda0
        movk xtmp, #0x4ebe, lsl #16 // 1321131424 = round(2^42 / MLKEM_Q)
        dup  mult.4s, wtmp

        block
        block
        block
        block
mlk_poly_compress_d11_end:

        ret

        .unreq in0
        .unreq in1
        .unreq in2
        .unreq in3
        .unreq in4
        .unreq in5
        .unreq in6
        .unreq in7
        .unreq t0
        .unreq out0
        .unreq out1
        .unreq out2
        .unreq out3
        .unreq out4
        .unreq out5
        .unreq out6
        .unreq out7
        .unreq last
        .unreq zero
        .unreq mult
        .unreq dst
        .unreq src
        .unreq xtmp
        .unreq wtmp

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && (!MLK_CONFIG_NO_ENCAPS_API || \
          !MLK_CONFIG_NO_DECAPS_API) && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || \
          MLKEM_K == 4) */
