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
  Name: poly_compress_d5_aarch64_asm
  Description: AArch64 polynomial compression (d=5)
  Signature: void mlk_poly_compress_d5_aarch64_asm(uint8_t r[160], const int16_t a[256], const uint8_t table[32])
  ABI:
    Architecture: aarch64
    CallingConvention: AAPCS64
    Features: [NEON]
    x0:
      type: buffer
      size_bytes: 160
      permissions: write-only
      c_parameter: uint8_t r[160]
      description: Output compressed polynomial
    x1:
      type: buffer
      size_bytes: 512
      permissions: read-only
      c_parameter: const int16_t a[256]
      description: Input polynomial
    x2:
      type: buffer
      size_bytes: 32
      permissions: read-only
      c_parameter: const uint8_t table[32]
      description: Constants (multiplier and index vectors)
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
 * Compress_5 @[FIPS203, Eq (4.7)] and ByteEncode_5
 * @[FIPS203, Algorithm 5] of a polynomial.
 *
 * For u in [0, MLKEM_Q - 1], y = sqrdmulh(u, 315) lies in [0, 32] and
 * Compress_5(u) = y mod 32, where 315 = round(2^20 / MLKEM_Q).
 *
 * LD2 splits 16 coefficients into even and odd ones. Three levels of SLI,
 * on 16-, 32- and 64-bit lanes, with TRN2 moving the upper half of a lane
 * down, pack 8 coefficients into the low 40 bits of each 64-bit lane. SLI
 * keeps only the low bits of the lower half, which reduces mod 32; excess
 * bits of the upper half end up above bit 40 and are not stored. TBL and
 * EXT then splice 64 coefficients into 40 contiguous output bytes.
 *
 * The table (x2) holds the multiplier and the TBL indices, see
 * mlk_aarch64_compress_d5_table.
 */

        e0     .req v0
        o0     .req v1
        e1     .req v2
        o1     .req v3
        e2     .req v4
        o2     .req v5
        e3     .req v6
        o3     .req v7

        t0     .req v16
        t1     .req v17
        t2     .req v18
        t3     .req v19

        // After gathering, out1 and out2 hold bytes 8..23 and 24..39 of
        // the block
        out1   .req v20
        out2   .req v21

        mult   .req v29 // mult and idx must be consecutive for LD1
        idx    .req v30

        dst   .req x0
        src   .req x1
        table .req x2
        count .req x3

// Compress the 8 coefficients in \x (16-bit lanes).
.macro compress x, mult
        sqrdmulh \x\().8h, \x\().8h, \mult\().8h
.endm

// Pack the 16 coefficients in \e (even) and \o (odd) into the low 40 bits
// of each 64-bit lane of \e. Clobbers \t.
.macro pack e, o, t
        sli  \e\().8h, \o\().8h, #5
        trn2 \t\().8h, \e\().8h, \e\().8h
        sli  \e\().4s, \t\().4s, #10
        trn2 \t\().4s, \e\().4s, \e\().4s
        sli  \e\().2d, \t\().2d, #20
.endm

// x0, ..., x3 hold a 40-byte block B0 B1 B2 B3 of the output,
// 10 bytes each, in their bytes 0..4 and 8..12. Leave output bytes 0..7
// in bytes 0..7 of x0, bytes 8..23 in o1 and bytes 24..39 in o2.
.macro gather o1, o2, x0, x1, x2, x3, idx
        // xk[0..9] = Bk, xk[10..15] = Bk[4..9]
        tbl  \x0\().16b, {\x0\().16b}, \idx\().16b
        tbl  \x1\().16b, {\x1\().16b}, \idx\().16b
        tbl  \x2\().16b, {\x2\().16b}, \idx\().16b
        tbl  \x3\().16b, {\x3\().16b}, \idx\().16b

        ext  \o1\().16b, \x0\().16b, \x1\().16b, #10   // B0[4..9] B1
        ext  \o1\().16b, \o1\().16b, \x2\().16b, #4    // B0[8..9] B1 B2[0..3]
        ext  \o2\().16b, \x2\().16b, \x3\().16b, #10   // B2[4..9] B3
.endm

        .text
        .global MLK_ASM_NAMESPACE(poly_compress_d5_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_compress_d5_aarch64_asm)

        // mult = round(2^20 / MLKEM_Q) = 315 in each 16-bit lane,
        // idx = [0,1,2,3,4,8,9,10, 11,12,4,8,9,10,11,12]
        ld1 {mult.16b, idx.16b}, [table]

        // Each iteration compresses 64 coefficients into 40 bytes
        mov count, #4
mlk_poly_compress_d5_loop_start:
        // ek, ok = even and odd coefficients of 16k .. 16k+15
        ld2 {e0.8h, o0.8h}, [src], #32
        ld2 {e1.8h, o1.8h}, [src], #32
        ld2 {e2.8h, o2.8h}, [src], #32
        ld2 {e3.8h, o3.8h}, [src], #32

        compress e0, mult
        compress o0, mult
        compress e1, mult
        compress o1, mult
        compress e2, mult
        compress o2, mult
        compress e3, mult
        compress o3, mult

        pack e0, o0, t0
        pack e1, o1, t1
        pack e2, o2, t2
        pack e3, o3, t3

        gather out1, out2, e0, e1, e2, e3, idx

        st1 {e0.8b}, [dst], #8
        st1 {out1.16b}, [dst], #16
        st1 {out2.16b}, [dst], #16

        subs count, count, #1
        cbnz count, mlk_poly_compress_d5_loop_start
        ret

        .unreq e0
        .unreq o0
        .unreq e1
        .unreq o1
        .unreq e2
        .unreq o2
        .unreq e3
        .unreq o3
        .unreq t0
        .unreq t1
        .unreq t2
        .unreq t3
        .unreq out1
        .unreq out2
        .unreq mult
        .unreq idx
        .unreq dst
        .unreq src
        .unreq table
        .unreq count

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && (!MLK_CONFIG_NO_ENCAPS_API || \
          !MLK_CONFIG_NO_DECAPS_API) && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || \
          MLKEM_K == 4) */
