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
  Name: poly_frombytes_aarch64_asm
  Description: Convert byte representation to polynomial
  Signature: void mlk_poly_frombytes_aarch64_asm(int16_t r[256], const uint8_t a[384])
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
      size_bytes: 384
      permissions: read-only
      c_parameter: const uint8_t a[384]
      description: Input byte array
  Stack:
    bytes: 0
*/

#include "../../../common.h"
#if defined(MLK_SYS_AARCH64_NEON) && \
    defined(MLK_ARITH_BACKEND_AARCH64) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (!defined(MLK_CONFIG_NO_ENCAPS_API) || \
     !defined(MLK_CONFIG_NO_DECAPS_API))
/* simpasm: header-end */

/*
 * ByteDecode_12 @[FIPS203, Algorithm 6] of a polynomial.
 *
 * Every 3 input bytes b0, b1, b2 hold two coefficients:
 *
 *   r[2i]   = b0 | (b1 & 0xf) << 8
 *   r[2i+1] = (b1 >> 4) | b2 << 4
 *
 * LD3 on byte lanes splits 48 input bytes into the vectors of b0, b1 and
 * b2. ZIP1/ZIP2 of b0 with the low nibbles of b1 (AND) form the even
 * coefficients, ZIP1/ZIP2 of b1 with b2 followed by USHR #4 the odd ones,
 * and ST2 on 16-bit lanes interleaves them.
 */

        dst     .req x0
        src     .req x1
        count   .req x2

        in0     .req v0 // in0, in1 and in2 must be consecutive for LD3
        in1     .req v1
        in2     .req v2
        lo1     .req v3
        even0   .req v4 // even0 and odd0 must be consecutive for ST2
        odd0    .req v5
        even1   .req v6 // even1 and odd1 must be consecutive for ST2
        odd1    .req v7
        mask    .req v16

// Form the 32 coefficients of the 48 input bytes split by LD3 into \b0,
// \b1, \b2 (bytes 3i, 3i + 1, 3i + 2): \e0, \e1 get the even coefficients
// b0 | (b1 & 0xf) << 8, and \o0, \o1 the odd coefficients
// (b1 >> 4) | b2 << 4, each for groups 0..7 and 8..15.
.macro unpack e0, e1, o0, o1, b0, b1, b2
        and  lo1.16b, \b1\().16b, mask.16b
        zip1 \e0\().16b, \b0\().16b, lo1.16b
        zip2 \e1\().16b, \b0\().16b, lo1.16b

        zip1 \o0\().16b, \b1\().16b, \b2\().16b
        zip2 \o1\().16b, \b1\().16b, \b2\().16b
        ushr \o0\().8h, \o0\().8h, #4
        ushr \o1\().8h, \o1\().8h, #4
.endm

        .text
        .global MLK_ASM_NAMESPACE(poly_frombytes_aarch64_asm)
        .balign 4
MLK_ASM_FN_SYMBOL(poly_frombytes_aarch64_asm)

        movi mask.16b, #0x0f

        // Each iteration decodes 48 bytes into 32 coefficients.
        mov count, #8
mlk_poly_frombytes_loop_start:
        ld3  {in0.16b, in1.16b, in2.16b}, [src], #48

        unpack even0, even1, odd0, odd1, in0, in1, in2

        st2  {even0.8h, odd0.8h}, [dst], #32
        st2  {even1.8h, odd1.8h}, [dst], #32

        subs count, count, #1
        cbnz count, mlk_poly_frombytes_loop_start
        ret

        .unreq dst
        .unreq src
        .unreq count
        .unreq in0
        .unreq in1
        .unreq in2
        .unreq lo1
        .unreq even0
        .unreq odd0
        .unreq even1
        .unreq odd1
        .unreq mask

/* simpasm: footer-start */
#endif /* MLK_SYS_AARCH64_NEON && MLK_ARITH_BACKEND_AARCH64 && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED && (!MLK_CONFIG_NO_ENCAPS_API || \
          !MLK_CONFIG_NO_DECAPS_API) */
