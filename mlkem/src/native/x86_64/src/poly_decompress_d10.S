/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [REF_AVX2]
 *   CRYSTALS-Kyber optimized AVX2 implementation
 *   Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/kyber/tree/main/avx2
 */

/*
 * This file is derived from the public domain
 * AVX2 Kyber implementation @[REF_AVX2].
 */

/*************************************************
 * Name:        mlk_poly_decompress_d10_avx2
 *
 * Description: Decompression of a polynomial from 10 bits per coefficient.
 *
 * Arguments:   - int16_t *r:       pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D10)
 *              - const int8_t *data: pointer to shufbidx constant
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/x86_64/src/poly_decompress_d10.S using scripts/simpasm. Do not modify it directly.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4
.global MLK_ASM_NAMESPACE(poly_decompress_d10_avx2)
MLK_ASM_FN_SYMBOL(poly_decompress_d10_avx2)

        .cfi_startproc
        movl	$0xd013404, %eax        # imm = 0xD013404
        vmovd	%eax, %xmm0
        vpbroadcastd	%xmm0, %ymm0
        movl	$0x4, %eax
        vmovq	%rax, %xmm1
        vpbroadcastq	%xmm1, %ymm1
        movl	$0x7fe01ff8, %eax       # imm = 0x7FE01FF8
        vmovd	%eax, %xmm2
        vpbroadcastd	%xmm2, %ymm2
        vmovdqa	(%rdx), %ymm3
        movl	$0xf, %ecx

Lpoly_decompress_d10_avx2_loop:
        vmovdqu	(%rsi), %ymm4
        vpermq	$0x94, %ymm4, %ymm4     # ymm4 = ymm4[0,1,1,2]
        vpshufb	%ymm3, %ymm4, %ymm4
        vpsllvd	%ymm1, %ymm4, %ymm4
        vpsrlw	$0x1, %ymm4, %ymm4
        vpand	%ymm2, %ymm4, %ymm4
        vpmulhrsw	%ymm0, %ymm4, %ymm4
        vmovdqu	%ymm4, (%rdi)
        addq	$0x14, %rsi
        addq	$0x20, %rdi
        decl	%ecx
        jne	Lpoly_decompress_d10_avx2_loop
        vmovdqu	(%rsi), %xmm4
        vmovd	0x10(%rsi), %xmm5
        vinserti128	$0x1, %xmm5, %ymm4, %ymm4
        vpermq	$0x94, %ymm4, %ymm4     # ymm4 = ymm4[0,1,1,2]
        vpshufb	%ymm3, %ymm4, %ymm4
        vpsllvd	%ymm1, %ymm4, %ymm4
        vpsrlw	$0x1, %ymm4, %ymm4
        vpand	%ymm2, %ymm4, %ymm4
        vpmulhrsw	%ymm0, %ymm4, %ymm4
        vmovdqu	%ymm4, (%rdi)
        retq
        .cfi_endproc

#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == \
          3) */
