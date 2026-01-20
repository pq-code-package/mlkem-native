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
 * Name:        mlk_poly_compress_d10_avx2
 *
 * Description: Compression of a polynomial to 10 bits per coefficient.
 *
 * Arguments:   - uint8_t *r:       pointer to output byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D10)
 *              - const int16_t *a: pointer to input polynomial
 *              - const int8_t *data: pointer to shufbidx constant
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || MLKEM_K == 3)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/x86_64/src/poly_compress_d10.S using scripts/simpasm. Do not modify it directly.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4
.global MLK_ASM_NAMESPACE(poly_compress_d10_avx2)
MLK_ASM_FN_SYMBOL(poly_compress_d10_avx2)

        .cfi_startproc
        movl	$0x4ebf4ebf, %eax       # imm = 0x4EBF4EBF
        vmovd	%eax, %xmm0
        vpbroadcastd	%xmm0, %ymm0
        vpsllw	$0x3, %ymm0, %ymm1
        movl	$0xf000f, %eax          # imm = 0xF000F
        vmovd	%eax, %xmm2
        vpbroadcastd	%xmm2, %ymm2
        movl	$0x10001000, %eax       # imm = 0x10001000
        vmovd	%eax, %xmm3
        vpbroadcastd	%xmm3, %ymm3
        movl	$0x3ff03ff, %eax        # imm = 0x3FF03FF
        vmovd	%eax, %xmm4
        vpbroadcastd	%xmm4, %ymm4
        movabsq	$0x400000104000001, %rax # imm = 0x400000104000001
        vmovq	%rax, %xmm5
        vpbroadcastq	%xmm5, %ymm5
        movl	$0xc, %eax
        vmovq	%rax, %xmm6
        vpbroadcastq	%xmm6, %ymm6
        vmovdqa	(%rdx), %ymm7
        movl	$0x10, %ecx

Lpoly_compress_d10_avx2_loop:
        vmovdqa	(%rsi), %ymm8
        vpmullw	%ymm1, %ymm8, %ymm9
        vpaddw	%ymm2, %ymm8, %ymm10
        vpsllw	$0x3, %ymm8, %ymm8
        vpmulhw	%ymm0, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm9, %ymm10
        vpandn	%ymm10, %ymm9, %ymm9
        vpsrlw	$0xf, %ymm9, %ymm9
        vpsubw	%ymm9, %ymm8, %ymm8
        vpmulhrsw	%ymm3, %ymm8, %ymm8
        vpand	%ymm4, %ymm8, %ymm8
        vpmaddwd	%ymm5, %ymm8, %ymm8
        vpsllvd	%ymm6, %ymm8, %ymm8
        vpsrlq	$0xc, %ymm8, %ymm8
        vpshufb	%ymm7, %ymm8, %ymm8
        vextracti128	$0x1, %ymm8, %xmm9
        vpblendw	$0xe0, %xmm9, %xmm8, %xmm8 # xmm8 = xmm8[0,1,2,3,4],xmm9[5,6,7]
        vmovdqu	%xmm8, (%rdi)
        vmovd	%xmm9, 0x10(%rdi)
        addq	$0x20, %rsi
        addq	$0x14, %rdi
        decl	%ecx
        jne	Lpoly_compress_d10_avx2_loop
        retq
        .cfi_endproc

#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == \
          3) */
