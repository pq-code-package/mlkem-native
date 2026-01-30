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
 * Name:        mlk_poly_decompress_d11_avx2
 *
 * Description: Decompression of a polynomial from 11 bits per coefficient.
 *
 * Arguments:   - int16_t *r:       pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D11)
 *              - const uint8_t *data: pointer to constants
 *                                  (shufbidx[0:32], srlvdidx[32:64],
 *                                   srlvqidx[64:96], shift[96:128])
 **************************************************/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/x86_64/src/poly_decompress_d11.S using scripts/simpasm. Do not modify it directly.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4
.global MLK_ASM_NAMESPACE(poly_decompress_d11_avx2)
MLK_ASM_FN_SYMBOL(poly_decompress_d11_avx2)

        .cfi_startproc
        movl	$0xd010d01, %eax        # imm = 0xD010D01
        vmovd	%eax, %xmm0
        vpbroadcastd	%xmm0, %ymm0
        movl	$0x7ff07ff0, %eax       # imm = 0x7FF07FF0
        vmovd	%eax, %xmm1
        vpbroadcastd	%xmm1, %ymm1
        vmovdqa	(%rdx), %ymm2
        vmovdqa	0x20(%rdx), %ymm3
        vmovdqa	0x40(%rdx), %ymm4
        vmovdqa	0x60(%rdx), %ymm5
        movl	$0xf, %ecx

Lpoly_decompress_d11_avx2_loop:
        vmovdqu	(%rsi), %ymm6
        vpermq	$0x94, %ymm6, %ymm6     # ymm6 = ymm6[0,1,1,2]
        vpshufb	%ymm2, %ymm6, %ymm6
        vpsrlvd	%ymm3, %ymm6, %ymm6
        vpsrlvq	%ymm4, %ymm6, %ymm6
        vpmullw	%ymm5, %ymm6, %ymm6
        vpsrlw	$0x1, %ymm6, %ymm6
        vpand	%ymm1, %ymm6, %ymm6
        vpmulhrsw	%ymm0, %ymm6, %ymm6
        vmovdqu	%ymm6, (%rdi)
        addq	$0x16, %rsi
        addq	$0x20, %rdi
        decl	%ecx
        jne	Lpoly_decompress_d11_avx2_loop
        vmovdqu	(%rsi), %xmm6
        movl	0x10(%rsi), %eax
        movzwl	0x14(%rsi), %r8d
        vmovd	%eax, %xmm7
        vpinsrw	$0x2, %r8d, %xmm7, %xmm7
        vinserti128	$0x1, %xmm7, %ymm6, %ymm6
        vpermq	$0x94, %ymm6, %ymm6     # ymm6 = ymm6[0,1,1,2]
        vpshufb	%ymm2, %ymm6, %ymm6
        vpsrlvd	%ymm3, %ymm6, %ymm6
        vpsrlvq	%ymm4, %ymm6, %ymm6
        vpmullw	%ymm5, %ymm6, %ymm6
        vpsrlw	$0x1, %ymm6, %ymm6
        vpand	%ymm1, %ymm6, %ymm6
        vpmulhrsw	%ymm0, %ymm6, %ymm6
        vmovdqu	%ymm6, (%rdi)
        retq
        .cfi_endproc

#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
