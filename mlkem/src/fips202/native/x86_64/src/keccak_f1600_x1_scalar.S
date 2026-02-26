/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) 2017-2024 The OpenSSL Project Authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* Keccak-f1600 permutation, scalar x86_64 implementation */
/* Based on https://github.com/awslabs/s2n-bignum/blob/main/x86/sha3/sha3_keccak_f1600.S */
/* Written by Andy Polyakov, @dot-asm, initially for the OpenSSL project */

#include "../../../../common.h"

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

#if defined(MLK_FIPS202_X86_64_X1_SCALAR) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/x86_64/src/keccak_f1600_x1_scalar.S using scripts/simpasm. Do not modify it directly.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4
.global MLK_ASM_NAMESPACE(keccak_f1600_x1_scalar)
MLK_ASM_FN_SYMBOL(keccak_f1600_x1_scalar)

        .cfi_startproc
        pushq	%rbx
        pushq	%rbp
        pushq	%r12
        pushq	%r13
        pushq	%r14
        pushq	%r15
        subq	$0xd0, %rsp
        .cfi_adjust_cfa_offset 0xd0
        notq	0x8(%rdi)
        notq	0x10(%rdi)
        notq	0x40(%rdi)
        notq	0x60(%rdi)
        notq	0x88(%rdi)
        notq	0xa0(%rdi)
        leaq	(%rsp), %r15
        movq	0xa0(%rdi), %rax
        movq	0xa8(%rdi), %rbx
        movq	0xb0(%rdi), %rcx
        movq	0xb8(%rdi), %rdx
        movq	0xc0(%rdi), %rbp
        movq	$0x0, %r8

Lkeccak_f1600_x1_scalar_loop:
        movq	%r8, 0xc8(%rsp)
        movq	(%rdi), %r8
        movq	0x30(%rdi), %r9
        movq	0x60(%rdi), %r10
        movq	0x90(%rdi), %r11
        xorq	0x10(%rdi), %rcx
        xorq	0x18(%rdi), %rdx
        xorq	%r8, %rax
        xorq	0x8(%rdi), %rbx
        xorq	0x38(%rdi), %rcx
        xorq	0x28(%rdi), %rax
        movq	%rbp, %r12
        xorq	0x20(%rdi), %rbp
        xorq	%r10, %rcx
        xorq	0x50(%rdi), %rax
        xorq	0x40(%rdi), %rdx
        xorq	%r9, %rbx
        xorq	0x48(%rdi), %rbp
        xorq	0x88(%rdi), %rcx
        xorq	0x78(%rdi), %rax
        xorq	0x68(%rdi), %rdx
        xorq	0x58(%rdi), %rbx
        xorq	0x70(%rdi), %rbp
        movq	%rcx, %r13
        rolq	%rcx
        xorq	%rax, %rcx
        xorq	%r11, %rdx
        rolq	%rax
        xorq	%rdx, %rax
        xorq	0x80(%rdi), %rbx
        rolq	%rdx
        xorq	%rbx, %rdx
        xorq	0x98(%rdi), %rbp
        rolq	%rbx
        xorq	%rbp, %rbx
        rolq	%rbp
        xorq	%r13, %rbp
        xorq	%rcx, %r9
        xorq	%rdx, %r10
        rolq	$0x2c, %r9
        xorq	%rbp, %r11
        xorq	%rax, %r12
        rolq	$0x2b, %r10
        xorq	%rbx, %r8
        movq	%r9, %r13
        rolq	$0x15, %r11
        orq	%r10, %r9
        xorq	%r8, %r9
        rolq	$0xe, %r12
        xorq	(%rsi), %r9
        movq	%r12, %r14
        andq	%r11, %r12
        movq	%r9, (%r15)
        xorq	%r10, %r12
        notq	%r10
        movq	%r12, 0x10(%r15)
        orq	%r11, %r10
        movq	0xb0(%rdi), %r12
        xorq	%r13, %r10
        movq	%r10, 0x8(%r15)
        andq	%r8, %r13
        movq	0x48(%rdi), %r9
        xorq	%r14, %r13
        movq	0x50(%rdi), %r10
        movq	%r13, 0x20(%r15)
        orq	%r8, %r14
        movq	0x18(%rdi), %r8
        xorq	%r11, %r14
        movq	0x80(%rdi), %r11
        movq	%r14, 0x18(%r15)
        xorq	%rbp, %r8
        xorq	%rdx, %r12
        rolq	$0x1c, %r8
        xorq	%rcx, %r11
        xorq	%rax, %r9
        rolq	$0x3d, %r12
        rolq	$0x2d, %r11
        xorq	%rbx, %r10
        rolq	$0x14, %r9
        movq	%r8, %r13
        orq	%r12, %r8
        rolq	$0x3, %r10
        xorq	%r11, %r8
        movq	%r8, 0x40(%r15)
        movq	%r9, %r14
        andq	%r13, %r9
        movq	0x8(%rdi), %r8
        xorq	%r12, %r9
        notq	%r12
        movq	%r9, 0x48(%r15)
        orq	%r11, %r12
        movq	0x38(%rdi), %r9
        xorq	%r10, %r12
        movq	%r12, 0x38(%r15)
        andq	%r10, %r11
        movq	0xa0(%rdi), %r12
        xorq	%r14, %r11
        movq	%r11, 0x30(%r15)
        orq	%r10, %r14
        movq	0x68(%rdi), %r10
        xorq	%r13, %r14
        movq	0x98(%rdi), %r11
        movq	%r14, 0x28(%r15)
        xorq	%rbp, %r10
        xorq	%rax, %r11
        rolq	$0x19, %r10
        xorq	%rdx, %r9
        rolq	$0x8, %r11
        xorq	%rbx, %r12
        rolq	$0x6, %r9
        xorq	%rcx, %r8
        rolq	$0x12, %r12
        movq	%r10, %r13
        andq	%r11, %r10
        rolq	%r8
        notq	%r11
        xorq	%r9, %r10
        movq	%r10, 0x58(%r15)
        movq	%r12, %r14
        andq	%r11, %r12
        movq	0x58(%rdi), %r10
        xorq	%r13, %r12
        movq	%r12, 0x60(%r15)
        orq	%r9, %r13
        movq	0xb8(%rdi), %r12
        xorq	%r8, %r13
        movq	%r13, 0x50(%r15)
        andq	%r8, %r9
        xorq	%r14, %r9
        movq	%r9, 0x70(%r15)
        orq	%r8, %r14
        movq	0x28(%rdi), %r9
        xorq	%r11, %r14
        movq	0x88(%rdi), %r11
        movq	%r14, 0x68(%r15)
        movq	0x20(%rdi), %r8
        xorq	%rcx, %r10
        xorq	%rdx, %r11
        rolq	$0xa, %r10
        xorq	%rbx, %r9
        rolq	$0xf, %r11
        xorq	%rbp, %r12
        rolq	$0x24, %r9
        xorq	%rax, %r8
        rolq	$0x38, %r12
        movq	%r10, %r13
        orq	%r11, %r10
        rolq	$0x1b, %r8
        notq	%r11
        xorq	%r9, %r10
        movq	%r10, 0x80(%r15)
        movq	%r12, %r14
        orq	%r11, %r12
        xorq	%r13, %r12
        movq	%r12, 0x88(%r15)
        andq	%r9, %r13
        xorq	%r8, %r13
        movq	%r13, 0x78(%r15)
        orq	%r8, %r9
        xorq	%r14, %r9
        movq	%r9, 0x98(%r15)
        andq	%r14, %r8
        xorq	%r11, %r8
        movq	%r8, 0x90(%r15)
        xorq	0x10(%rdi), %rdx
        xorq	0x40(%rdi), %rbp
        rolq	$0x3e, %rdx
        xorq	0xa8(%rdi), %rcx
        rolq	$0x37, %rbp
        xorq	0x70(%rdi), %rax
        rolq	$0x2, %rcx
        xorq	0x78(%rdi), %rbx
        xchgq	%rdi, %r15
        rolq	$0x27, %rax
        rolq	$0x29, %rbx
        movq	%rdx, %r13
        andq	%rbp, %rdx
        notq	%rbp
        xorq	%rcx, %rdx
        movq	%rdx, 0xc0(%rdi)
        movq	%rax, %r14
        andq	%rbp, %rax
        xorq	%r13, %rax
        movq	%rax, 0xa0(%rdi)
        orq	%rcx, %r13
        xorq	%rbx, %r13
        movq	%r13, 0xb8(%rdi)
        andq	%rbx, %rcx
        xorq	%r14, %rcx
        movq	%rcx, 0xb0(%rdi)
        orq	%r14, %rbx
        xorq	%rbp, %rbx
        movq	%rbx, 0xa8(%rdi)
        movq	%rdx, %rbp
        movq	%r13, %rdx
        leaq	0x8(%rsi), %rsi
        movq	(%rdi), %r8
        movq	0x30(%rdi), %r9
        movq	0x60(%rdi), %r10
        movq	0x90(%rdi), %r11
        xorq	0x10(%rdi), %rcx
        xorq	0x18(%rdi), %rdx
        xorq	%r8, %rax
        xorq	0x8(%rdi), %rbx
        xorq	0x38(%rdi), %rcx
        xorq	0x28(%rdi), %rax
        movq	%rbp, %r12
        xorq	0x20(%rdi), %rbp
        xorq	%r10, %rcx
        xorq	0x50(%rdi), %rax
        xorq	0x40(%rdi), %rdx
        xorq	%r9, %rbx
        xorq	0x48(%rdi), %rbp
        xorq	0x88(%rdi), %rcx
        xorq	0x78(%rdi), %rax
        xorq	0x68(%rdi), %rdx
        xorq	0x58(%rdi), %rbx
        xorq	0x70(%rdi), %rbp
        movq	%rcx, %r13
        rolq	%rcx
        xorq	%rax, %rcx
        xorq	%r11, %rdx
        rolq	%rax
        xorq	%rdx, %rax
        xorq	0x80(%rdi), %rbx
        rolq	%rdx
        xorq	%rbx, %rdx
        xorq	0x98(%rdi), %rbp
        rolq	%rbx
        xorq	%rbp, %rbx
        rolq	%rbp
        xorq	%r13, %rbp
        xorq	%rcx, %r9
        xorq	%rdx, %r10
        rolq	$0x2c, %r9
        xorq	%rbp, %r11
        xorq	%rax, %r12
        rolq	$0x2b, %r10
        xorq	%rbx, %r8
        movq	%r9, %r13
        rolq	$0x15, %r11
        orq	%r10, %r9
        xorq	%r8, %r9
        rolq	$0xe, %r12
        xorq	(%rsi), %r9
        movq	%r12, %r14
        andq	%r11, %r12
        movq	%r9, (%r15)
        xorq	%r10, %r12
        notq	%r10
        movq	%r12, 0x10(%r15)
        orq	%r11, %r10
        movq	0xb0(%rdi), %r12
        xorq	%r13, %r10
        movq	%r10, 0x8(%r15)
        andq	%r8, %r13
        movq	0x48(%rdi), %r9
        xorq	%r14, %r13
        movq	0x50(%rdi), %r10
        movq	%r13, 0x20(%r15)
        orq	%r8, %r14
        movq	0x18(%rdi), %r8
        xorq	%r11, %r14
        movq	0x80(%rdi), %r11
        movq	%r14, 0x18(%r15)
        xorq	%rbp, %r8
        xorq	%rdx, %r12
        rolq	$0x1c, %r8
        xorq	%rcx, %r11
        xorq	%rax, %r9
        rolq	$0x3d, %r12
        rolq	$0x2d, %r11
        xorq	%rbx, %r10
        rolq	$0x14, %r9
        movq	%r8, %r13
        orq	%r12, %r8
        rolq	$0x3, %r10
        xorq	%r11, %r8
        movq	%r8, 0x40(%r15)
        movq	%r9, %r14
        andq	%r13, %r9
        movq	0x8(%rdi), %r8
        xorq	%r12, %r9
        notq	%r12
        movq	%r9, 0x48(%r15)
        orq	%r11, %r12
        movq	0x38(%rdi), %r9
        xorq	%r10, %r12
        movq	%r12, 0x38(%r15)
        andq	%r10, %r11
        movq	0xa0(%rdi), %r12
        xorq	%r14, %r11
        movq	%r11, 0x30(%r15)
        orq	%r10, %r14
        movq	0x68(%rdi), %r10
        xorq	%r13, %r14
        movq	0x98(%rdi), %r11
        movq	%r14, 0x28(%r15)
        xorq	%rbp, %r10
        xorq	%rax, %r11
        rolq	$0x19, %r10
        xorq	%rdx, %r9
        rolq	$0x8, %r11
        xorq	%rbx, %r12
        rolq	$0x6, %r9
        xorq	%rcx, %r8
        rolq	$0x12, %r12
        movq	%r10, %r13
        andq	%r11, %r10
        rolq	%r8
        notq	%r11
        xorq	%r9, %r10
        movq	%r10, 0x58(%r15)
        movq	%r12, %r14
        andq	%r11, %r12
        movq	0x58(%rdi), %r10
        xorq	%r13, %r12
        movq	%r12, 0x60(%r15)
        orq	%r9, %r13
        movq	0xb8(%rdi), %r12
        xorq	%r8, %r13
        movq	%r13, 0x50(%r15)
        andq	%r8, %r9
        xorq	%r14, %r9
        movq	%r9, 0x70(%r15)
        orq	%r8, %r14
        movq	0x28(%rdi), %r9
        xorq	%r11, %r14
        movq	0x88(%rdi), %r11
        movq	%r14, 0x68(%r15)
        movq	0x20(%rdi), %r8
        xorq	%rcx, %r10
        xorq	%rdx, %r11
        rolq	$0xa, %r10
        xorq	%rbx, %r9
        rolq	$0xf, %r11
        xorq	%rbp, %r12
        rolq	$0x24, %r9
        xorq	%rax, %r8
        rolq	$0x38, %r12
        movq	%r10, %r13
        orq	%r11, %r10
        rolq	$0x1b, %r8
        notq	%r11
        xorq	%r9, %r10
        movq	%r10, 0x80(%r15)
        movq	%r12, %r14
        orq	%r11, %r12
        xorq	%r13, %r12
        movq	%r12, 0x88(%r15)
        andq	%r9, %r13
        xorq	%r8, %r13
        movq	%r13, 0x78(%r15)
        orq	%r8, %r9
        xorq	%r14, %r9
        movq	%r9, 0x98(%r15)
        andq	%r14, %r8
        xorq	%r11, %r8
        movq	%r8, 0x90(%r15)
        xorq	0x10(%rdi), %rdx
        xorq	0x40(%rdi), %rbp
        rolq	$0x3e, %rdx
        xorq	0xa8(%rdi), %rcx
        rolq	$0x37, %rbp
        xorq	0x70(%rdi), %rax
        rolq	$0x2, %rcx
        xorq	0x78(%rdi), %rbx
        xchgq	%rdi, %r15
        rolq	$0x27, %rax
        rolq	$0x29, %rbx
        movq	%rdx, %r13
        andq	%rbp, %rdx
        notq	%rbp
        xorq	%rcx, %rdx
        movq	%rdx, 0xc0(%rdi)
        movq	%rax, %r14
        andq	%rbp, %rax
        xorq	%r13, %rax
        movq	%rax, 0xa0(%rdi)
        orq	%rcx, %r13
        xorq	%rbx, %r13
        movq	%r13, 0xb8(%rdi)
        andq	%rbx, %rcx
        xorq	%r14, %rcx
        movq	%rcx, 0xb0(%rdi)
        orq	%r14, %rbx
        xorq	%rbp, %rbx
        movq	%rbx, 0xa8(%rdi)
        movq	%rdx, %rbp
        movq	%r13, %rdx
        leaq	0x8(%rsi), %rsi
        movq	0xc8(%rsp), %r8
        addq	$0x2, %r8
        cmpq	$0x18, %r8
        jne	Lkeccak_f1600_x1_scalar_loop
        leaq	-0xc0(%rsi), %rsi
        notq	0x8(%rdi)
        notq	0x10(%rdi)
        notq	0x40(%rdi)
        notq	0x60(%rdi)
        notq	0x88(%rdi)
        notq	0xa0(%rdi)
        addq	$0xd0, %rsp
        .cfi_adjust_cfa_offset -0xd0
        popq	%r15
        popq	%r14
        popq	%r13
        popq	%r12
        popq	%rbp
        popq	%rbx
        retq
        .cfi_endproc

MLK_ASM_FN_SIZE(keccak_f1600_x1_scalar)

#endif /* MLK_FIPS202_X86_64_X1_SCALAR && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
