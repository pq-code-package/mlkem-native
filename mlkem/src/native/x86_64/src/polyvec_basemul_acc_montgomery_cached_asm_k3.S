/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 3)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/x86_64/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k3)
MLK_ASM_FN_SYMBOL(polyvec_basemul_acc_montgomery_cached_asm_k3)

        vmovdqa	(%r8), %ymm0
        vmovdqa	0x20(%r8), %ymm1
        vmovdqa	(%rsi), %ymm2
        vmovdqa	0x20(%rsi), %ymm3
        vmovdqa	(%rdx), %ymm4
        vmovdqa	0x20(%rdx), %ymm5
        vmovdqa	(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, (%rdi)
        vmovdqa	%ymm9, 0x20(%rdi)
        vmovdqa	0x40(%rsi), %ymm2
        vmovdqa	0x60(%rsi), %ymm3
        vmovdqa	0x40(%rdx), %ymm4
        vmovdqa	0x60(%rdx), %ymm5
        vmovdqa	0x20(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x40(%rdi)
        vmovdqa	%ymm9, 0x60(%rdi)
        vmovdqa	0x80(%rsi), %ymm2
        vmovdqa	0xa0(%rsi), %ymm3
        vmovdqa	0x80(%rdx), %ymm4
        vmovdqa	0xa0(%rdx), %ymm5
        vmovdqa	0x40(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x80(%rdi)
        vmovdqa	%ymm9, 0xa0(%rdi)
        vmovdqa	0xc0(%rsi), %ymm2
        vmovdqa	0xe0(%rsi), %ymm3
        vmovdqa	0xc0(%rdx), %ymm4
        vmovdqa	0xe0(%rdx), %ymm5
        vmovdqa	0x60(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0xc0(%rdi)
        vmovdqa	%ymm9, 0xe0(%rdi)
        vmovdqa	0x100(%rsi), %ymm2
        vmovdqa	0x120(%rsi), %ymm3
        vmovdqa	0x100(%rdx), %ymm4
        vmovdqa	0x120(%rdx), %ymm5
        vmovdqa	0x80(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x100(%rdi)
        vmovdqa	%ymm9, 0x120(%rdi)
        vmovdqa	0x140(%rsi), %ymm2
        vmovdqa	0x160(%rsi), %ymm3
        vmovdqa	0x140(%rdx), %ymm4
        vmovdqa	0x160(%rdx), %ymm5
        vmovdqa	0xa0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x140(%rdi)
        vmovdqa	%ymm9, 0x160(%rdi)
        vmovdqa	0x180(%rsi), %ymm2
        vmovdqa	0x1a0(%rsi), %ymm3
        vmovdqa	0x180(%rdx), %ymm4
        vmovdqa	0x1a0(%rdx), %ymm5
        vmovdqa	0xc0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x180(%rdi)
        vmovdqa	%ymm9, 0x1a0(%rdi)
        vmovdqa	0x1c0(%rsi), %ymm2
        vmovdqa	0x1e0(%rsi), %ymm3
        vmovdqa	0x1c0(%rdx), %ymm4
        vmovdqa	0x1e0(%rdx), %ymm5
        vmovdqa	0xe0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x1c0(%rdi)
        vmovdqa	%ymm9, 0x1e0(%rdi)
        vmovdqa	0x200(%rsi), %ymm2
        vmovdqa	0x220(%rsi), %ymm3
        vmovdqa	0x200(%rdx), %ymm4
        vmovdqa	0x220(%rdx), %ymm5
        vmovdqa	0x100(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	(%rdi), %ymm8
        vmovdqa	0x20(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, (%rdi)
        vmovdqa	%ymm9, 0x20(%rdi)
        vmovdqa	0x240(%rsi), %ymm2
        vmovdqa	0x260(%rsi), %ymm3
        vmovdqa	0x240(%rdx), %ymm4
        vmovdqa	0x260(%rdx), %ymm5
        vmovdqa	0x120(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x40(%rdi), %ymm8
        vmovdqa	0x60(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x40(%rdi)
        vmovdqa	%ymm9, 0x60(%rdi)
        vmovdqa	0x280(%rsi), %ymm2
        vmovdqa	0x2a0(%rsi), %ymm3
        vmovdqa	0x280(%rdx), %ymm4
        vmovdqa	0x2a0(%rdx), %ymm5
        vmovdqa	0x140(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x80(%rdi), %ymm8
        vmovdqa	0xa0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x80(%rdi)
        vmovdqa	%ymm9, 0xa0(%rdi)
        vmovdqa	0x2c0(%rsi), %ymm2
        vmovdqa	0x2e0(%rsi), %ymm3
        vmovdqa	0x2c0(%rdx), %ymm4
        vmovdqa	0x2e0(%rdx), %ymm5
        vmovdqa	0x160(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0xc0(%rdi), %ymm8
        vmovdqa	0xe0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0xc0(%rdi)
        vmovdqa	%ymm9, 0xe0(%rdi)
        vmovdqa	0x300(%rsi), %ymm2
        vmovdqa	0x320(%rsi), %ymm3
        vmovdqa	0x300(%rdx), %ymm4
        vmovdqa	0x320(%rdx), %ymm5
        vmovdqa	0x180(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x100(%rdi), %ymm8
        vmovdqa	0x120(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x100(%rdi)
        vmovdqa	%ymm9, 0x120(%rdi)
        vmovdqa	0x340(%rsi), %ymm2
        vmovdqa	0x360(%rsi), %ymm3
        vmovdqa	0x340(%rdx), %ymm4
        vmovdqa	0x360(%rdx), %ymm5
        vmovdqa	0x1a0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x140(%rdi), %ymm8
        vmovdqa	0x160(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x140(%rdi)
        vmovdqa	%ymm9, 0x160(%rdi)
        vmovdqa	0x380(%rsi), %ymm2
        vmovdqa	0x3a0(%rsi), %ymm3
        vmovdqa	0x380(%rdx), %ymm4
        vmovdqa	0x3a0(%rdx), %ymm5
        vmovdqa	0x1c0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x180(%rdi), %ymm8
        vmovdqa	0x1a0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x180(%rdi)
        vmovdqa	%ymm9, 0x1a0(%rdi)
        vmovdqa	0x3c0(%rsi), %ymm2
        vmovdqa	0x3e0(%rsi), %ymm3
        vmovdqa	0x3c0(%rdx), %ymm4
        vmovdqa	0x3e0(%rdx), %ymm5
        vmovdqa	0x1e0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x1c0(%rdi), %ymm8
        vmovdqa	0x1e0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x1c0(%rdi)
        vmovdqa	%ymm9, 0x1e0(%rdi)
        vmovdqa	0x400(%rsi), %ymm2
        vmovdqa	0x420(%rsi), %ymm3
        vmovdqa	0x400(%rdx), %ymm4
        vmovdqa	0x420(%rdx), %ymm5
        vmovdqa	0x200(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	(%rdi), %ymm8
        vmovdqa	0x20(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, (%rdi)
        vmovdqa	%ymm9, 0x20(%rdi)
        vmovdqa	0x440(%rsi), %ymm2
        vmovdqa	0x460(%rsi), %ymm3
        vmovdqa	0x440(%rdx), %ymm4
        vmovdqa	0x460(%rdx), %ymm5
        vmovdqa	0x220(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x40(%rdi), %ymm8
        vmovdqa	0x60(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x40(%rdi)
        vmovdqa	%ymm9, 0x60(%rdi)
        vmovdqa	0x480(%rsi), %ymm2
        vmovdqa	0x4a0(%rsi), %ymm3
        vmovdqa	0x480(%rdx), %ymm4
        vmovdqa	0x4a0(%rdx), %ymm5
        vmovdqa	0x240(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x80(%rdi), %ymm8
        vmovdqa	0xa0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x80(%rdi)
        vmovdqa	%ymm9, 0xa0(%rdi)
        vmovdqa	0x4c0(%rsi), %ymm2
        vmovdqa	0x4e0(%rsi), %ymm3
        vmovdqa	0x4c0(%rdx), %ymm4
        vmovdqa	0x4e0(%rdx), %ymm5
        vmovdqa	0x260(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0xc0(%rdi), %ymm8
        vmovdqa	0xe0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0xc0(%rdi)
        vmovdqa	%ymm9, 0xe0(%rdi)
        vmovdqa	0x500(%rsi), %ymm2
        vmovdqa	0x520(%rsi), %ymm3
        vmovdqa	0x500(%rdx), %ymm4
        vmovdqa	0x520(%rdx), %ymm5
        vmovdqa	0x280(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x100(%rdi), %ymm8
        vmovdqa	0x120(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x100(%rdi)
        vmovdqa	%ymm9, 0x120(%rdi)
        vmovdqa	0x540(%rsi), %ymm2
        vmovdqa	0x560(%rsi), %ymm3
        vmovdqa	0x540(%rdx), %ymm4
        vmovdqa	0x560(%rdx), %ymm5
        vmovdqa	0x2a0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x140(%rdi), %ymm8
        vmovdqa	0x160(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x140(%rdi)
        vmovdqa	%ymm9, 0x160(%rdi)
        vmovdqa	0x580(%rsi), %ymm2
        vmovdqa	0x5a0(%rsi), %ymm3
        vmovdqa	0x580(%rdx), %ymm4
        vmovdqa	0x5a0(%rdx), %ymm5
        vmovdqa	0x2c0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm8, %ymm13, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x180(%rdi), %ymm8
        vmovdqa	0x1a0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x180(%rdi)
        vmovdqa	%ymm9, 0x1a0(%rdi)
        vmovdqa	0x5c0(%rsi), %ymm2
        vmovdqa	0x5e0(%rsi), %ymm3
        vmovdqa	0x5c0(%rdx), %ymm4
        vmovdqa	0x5e0(%rdx), %ymm5
        vmovdqa	0x2e0(%rcx), %ymm6
        vpmullw	%ymm2, %ymm1, %ymm13
        vpmullw	%ymm3, %ymm1, %ymm14
        vpmullw	%ymm13, %ymm4, %ymm7
        vpmullw	%ymm13, %ymm5, %ymm9
        vpmullw	%ymm14, %ymm6, %ymm8
        vpmullw	%ymm14, %ymm4, %ymm10
        vpmulhw	%ymm7, %ymm0, %ymm7
        vpmulhw	%ymm9, %ymm0, %ymm9
        vpmulhw	%ymm8, %ymm0, %ymm8
        vpmulhw	%ymm10, %ymm0, %ymm10
        vpmulhw	%ymm2, %ymm4, %ymm11
        vpmulhw	%ymm2, %ymm5, %ymm12
        vpmulhw	%ymm3, %ymm6, %ymm13
        vpmulhw	%ymm3, %ymm4, %ymm14
        vpsubw	%ymm7, %ymm11, %ymm7
        vpsubw	%ymm9, %ymm12, %ymm9
        vpsubw	%ymm13, %ymm8, %ymm8
        vpsubw	%ymm10, %ymm14, %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	0x1c0(%rdi), %ymm8
        vmovdqa	0x1e0(%rdi), %ymm10
        vpaddw	%ymm7, %ymm8, %ymm7
        vpaddw	%ymm9, %ymm10, %ymm9
        vmovdqa	%ymm7, 0x1c0(%rdi)
        vmovdqa	%ymm9, 0x1e0(%rdi)
        retq

#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 3) */
