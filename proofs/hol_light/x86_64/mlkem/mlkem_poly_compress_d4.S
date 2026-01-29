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
 * Name:        mlk_poly_compress_d4_avx2_avx2
 *
 * Description: Compression of a polynomial vector to 4 bits per coefficient.
 *
 * Arguments:   - uint8_t *r:       pointer to output byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES_D4)
 *              - const int16_t *a: pointer to input polynomial
 *              - const int32_t *data: pointer to qdata containing permdidx
 **************************************************/


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/x86_64/src/poly_compress_d4.S using scripts/simpasm. Do not modify it directly.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4
#ifdef __APPLE__
.global _PQCP_MLKEM_NATIVE_MLKEM768_poly_compress_d4_avx2
_PQCP_MLKEM_NATIVE_MLKEM768_poly_compress_d4_avx2:
#else
.global PQCP_MLKEM_NATIVE_MLKEM768_poly_compress_d4_avx2
PQCP_MLKEM_NATIVE_MLKEM768_poly_compress_d4_avx2:
#endif

        .cfi_startproc
        endbr64
        movl	$0x4ebf4ebf, %eax       # imm = 0x4EBF4EBF
        vmovd	%eax, %xmm0
        vpbroadcastd	%xmm0, %ymm0
        movl	$0x2000200, %eax        # imm = 0x2000200
        vmovd	%eax, %xmm1
        vpbroadcastd	%xmm1, %ymm1
        movl	$0xf000f, %eax          # imm = 0xF000F
        vmovd	%eax, %xmm2
        vpbroadcastd	%xmm2, %ymm2
        movl	$0x10011001, %eax       # imm = 0x10011001
        vmovd	%eax, %xmm3
        vpbroadcastd	%xmm3, %ymm3
        vmovdqa	(%rdx), %ymm4
        movl	$0x4, %ecx

Lpoly_compress_d4_avx2_loop:
        vmovdqa	(%rsi), %ymm5
        vmovdqa	0x20(%rsi), %ymm6
        vmovdqa	0x40(%rsi), %ymm7
        vmovdqa	0x60(%rsi), %ymm8
        vpmulhw	%ymm0, %ymm5, %ymm5
        vpmulhw	%ymm0, %ymm6, %ymm6
        vpmulhw	%ymm0, %ymm7, %ymm7
        vpmulhw	%ymm0, %ymm8, %ymm8
        vpmulhrsw	%ymm1, %ymm5, %ymm5
        vpmulhrsw	%ymm1, %ymm6, %ymm6
        vpmulhrsw	%ymm1, %ymm7, %ymm7
        vpmulhrsw	%ymm1, %ymm8, %ymm8
        vpand	%ymm2, %ymm5, %ymm5
        vpand	%ymm2, %ymm6, %ymm6
        vpand	%ymm2, %ymm7, %ymm7
        vpand	%ymm2, %ymm8, %ymm8
        vpackuswb	%ymm6, %ymm5, %ymm5
        vpackuswb	%ymm8, %ymm7, %ymm7
        vpmaddubsw	%ymm3, %ymm5, %ymm5
        vpmaddubsw	%ymm3, %ymm7, %ymm7
        vpackuswb	%ymm7, %ymm5, %ymm5
        vpermd	%ymm5, %ymm4, %ymm5
        vmovdqu	%ymm5, (%rdi)
        addq	$0x80, %rsi
        addq	$0x20, %rdi
        decl	%ecx
        jne	Lpoly_compress_d4_avx2_loop
        retq
        .cfi_endproc
