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
  Name: poly_compress_d10_aarch64_asm
  Description: AArch64 polynomial compression (d=10)
  Signature: void mlk_poly_compress_d10_aarch64_asm(uint8_t r[320], const int16_t a[256])
  ABI:
    Architecture: aarch64
    CallingConvention: AAPCS64
    Features: [NEON]
    x0:
      type: buffer
      size_bytes: 320
      permissions: write-only
      c_parameter: uint8_t r[320]
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
 * Compress_10 @[FIPS203, Eq (4.7)] and ByteEncode_10
 * @[FIPS203, Algorithm 5] of a polynomial.
 *
 * For u in [0, MLKEM_Q - 1], y = sqrdmulh(u, 660565712) on 32-bit lanes
 * lies in [0, 1024] and Compress_10(u) = y mod 2^10, where
 * 660565712 = round(2^41 / MLKEM_Q).
 *
 * TRN1/TRN2 against zero widen even and odd coefficients to 32-bit lanes.
 * Two levels of SLI pack 4 coefficients into the low 40 bits of each
 * 64-bit lane, reducing mod 2^10, and TBL moves the 10 output bytes of a
 * vector to its bytes 0..9.
 *
 * Each vector is written by a 16-byte store whose last 6 bytes are
 * overwritten by the next store, so the stores must stay in increasing
 * address order. To not write past the end of an 80-byte block, the last
 * vector is joined with the tail of the previous one (EXT) and stored at
 * offset 64.
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

        t0     .req v16
        last   .req v17

        zero   .req v24
        mult   .req v25
        idx    .req v26

        dst    .req x0
        src    .req x1
        xtmp   .req x3
        wtmp   .req w3
        xtmp2  .req x4

// x[0], ..., x[7] -> even coefficients in the 32-bit lanes of x, odd ones in
// the 32-bit lanes of t; y = sqrdmulh(u, M) with M = round(2^41 / MLKEM_Q)
.macro compress x, t
        trn2     \t\().8h, \x\().8h, zero.8h
        trn1     \x\().8h, \x\().8h, zero.8h
        sqrdmulh \x\().4s, \x\().4s, mult.4s
        sqrdmulh \t\().4s, \t\().4s, mult.4s
.endm

// p[i] = (y[2i] mod 2^10) | y[2i+1] << 10 in the 32-bit lanes of x,
// then g[i] = (p[2i] mod 2^20) | p[2i+1] << 20 in the 64-bit lanes of x
.macro pack x, t
        sli  \x\().4s, \t\().4s, #10
        trn2 \t\().4s, \x\().4s, zero.4s
        sli  \x\().2d, \t\().2d, #20
.endm

// bytes 0..4 and 8..12 of x -> bytes 0..9; bytes 10..15 = bytes 4..9
.macro compact x
        tbl  \x\().16b, {\x\().16b}, idx.16b
.endm

// Compress the 64 coefficients at src + off into 80 bytes at dst;
// dst advances by 80
.macro block off
        ldr q_in0, [src, #(\off)]
        ldr q_in1, [src, #(\off + 16)]
        ldr q_in2, [src, #(\off + 32)]
        ldr q_in3, [src, #(\off + 48)]
        ldr q_in4, [src, #(\off + 64)]
        ldr q_in5, [src, #(\off + 80)]
        ldr q_in6, [src, #(\off + 96)]
        ldr q_in7, [src, #(\off + 112)]

        compress in0, t0
        pack     in0, t0
        compact  in0
        compress in1, t0
        pack     in1, t0
        compact  in1
        compress in2, t0
        pack     in2, t0
        compact  in2
        compress in3, t0
        pack     in3, t0
        compact  in3
        compress in4, t0
        pack     in4, t0
        compact  in4
        compress in5, t0
        pack     in5, t0
        compact  in5
        compress in6, t0
        pack     in6, t0
        compact  in6
        compress in7, t0
        pack     in7, t0
        compact  in7

        // output bytes 64..79 of the block
        ext  last.16b, in6.16b, in7.16b, #10

        st1 {in0.16b}, [dst], #16
        sub dst, dst, #6
        st1 {in1.16b}, [dst], #16
        sub dst, dst, #6
        st1 {in2.16b}, [dst], #16
        sub dst, dst, #6
        st1 {in3.16b}, [dst], #16
        sub dst, dst, #6
        st1 {in4.16b}, [dst], #16
        sub dst, dst, #6
        st1 {in5.16b}, [dst], #16
        sub dst, dst, #6
        st1 {in6.16b}, [dst], #16
        sub dst, dst, #12
        st1 {last.16b}, [dst], #16
.endm

        .text
        .global MLK_ASM_NAMESPACE(poly_compress_d10_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d10_aarch64_asm)

mlk_poly_compress_d10_start:
        movi zero.2d, #0

        mov  xtmp, #0x6ed0
        movk xtmp, #0x275f, lsl #16 // 660565712 = round(2^41 / MLKEM_Q)
        dup  mult.4s, wtmp

        // idx = [0,1,2,3,4,8,9,10, 11,12,4,8,9,10,11,12]
        mov  xtmp, #0x0100
        movk xtmp, #0x0302, lsl #16
        movk xtmp, #0x0804, lsl #32
        movk xtmp, #0x0a09, lsl #48
        mov  xtmp2, #0x0c0b
        movk xtmp2, #0x0804, lsl #16
        movk xtmp2, #0x0a09, lsl #32
        movk xtmp2, #0x0c0b, lsl #48
        dup  idx.2d, xtmp
        dup  t0.2d, xtmp2
        zip1 idx.2d, idx.2d, t0.2d

        block 0
        block 128
        block 256
        block 384
mlk_poly_compress_d10_end:

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
        .unreq t0
        .unreq last
        .unreq zero
        .unreq mult
        .unreq idx
        .unreq dst
        .unreq src
        .unreq xtmp
        .unreq wtmp
        .unreq xtmp2

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && (!MLK_CONFIG_NO_ENCAPS_API || \
          !MLK_CONFIG_NO_DECAPS_API) && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || \
          MLKEM_K == 2 || MLKEM_K == 3) */
