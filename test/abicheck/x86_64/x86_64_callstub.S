/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Function: asm_call_stub_x86_64_sysv
 * Description: x86_64 System V ABI compliance testing stub
 *
 * C Signature: void asm_call_stub_x86_64_sysv(
 *     struct x86_64_register_state *input,   // rdi
 *     struct x86_64_register_state *output,   // rsi
 *     void (*function_ptr)(void))             // rdx
 *
 * struct x86_64_register_state layout (14 * 8 = 112 bytes):
 *   offset  0: rdi    offset 48: rax
 *   offset  8: rsi    offset 56: rbx
 *   offset 16: rdx    offset 64: rbp
 *   offset 24: rcx    offset 72: r12
 *   offset 32: r8     offset 80: r13
 *   offset 40: r9     offset 88: r14
 *                      offset 96: r15
 *                      offset 104: r10
 *
 * Callee-saved in System V: rbx, rbp, r12-r15
 *
 * Stack layout after prologue (16-byte aligned; alignment math at the
 * subq below):
 *   [rsp+ 0]: alignment padding
 *   [rsp+ 8]: output state ptr
 *   [rsp+16]: function ptr
 *   [rsp+24]: saved rbx
 *   [rsp+32]: saved rbp
 *   [rsp+40]: saved r12
 *   [rsp+48]: saved r13
 *   [rsp+56]: saved r14
 *   [rsp+64]: saved r15
 *   [rsp+72]: return address
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 16
#ifdef __APPLE__
.global _asm_call_stub_x86_64_sysv
_asm_call_stub_x86_64_sysv:
#else
.global asm_call_stub_x86_64_sysv
asm_call_stub_x86_64_sysv:
#endif
        .cfi_startproc
        /* Save callee-saved registers */
        pushq   %r15
        .cfi_adjust_cfa_offset 8
        .cfi_offset %r15, -16
        pushq   %r14
        .cfi_adjust_cfa_offset 8
        .cfi_offset %r14, -24
        pushq   %r13
        .cfi_adjust_cfa_offset 8
        .cfi_offset %r13, -32
        pushq   %r12
        .cfi_adjust_cfa_offset 8
        .cfi_offset %r12, -40
        pushq   %rbp
        .cfi_adjust_cfa_offset 8
        .cfi_offset %rbp, -48
        pushq   %rbx
        .cfi_adjust_cfa_offset 8
        .cfi_offset %rbx, -56

        /* 16 bytes for the two pointers + 8 padding; keeps %rsp 16-byte
         * aligned at the inner call (entry %rsp%16==8, +6 pushes +24 = 80,
         * 80%16==0; SysV). */
        subq    $24, %rsp
        .cfi_adjust_cfa_offset 24

        /* Save output state ptr and function ptr to stack. */
        movq    %rsi, 8(%rsp)    /* output state ptr */
        movq    %rdx, 16(%rsp)   /* function ptr */

        /* rdi still points to input state - load all registers from it */
        /* Load non-argument registers first */
        movq     48(%rdi), %rax
        movq     56(%rdi), %rbx
        movq     64(%rdi), %rbp
        movq     72(%rdi), %r12
        movq     80(%rdi), %r13
        movq     88(%rdi), %r14
        movq     96(%rdi), %r15
        movq    104(%rdi), %r10

        /* Load argument registers (rdi last since it's our base) */
        movq      8(%rdi), %rsi
        movq     16(%rdi), %rdx
        movq     24(%rdi), %rcx
        movq     32(%rdi), %r8
        movq     40(%rdi), %r9
        movq      0(%rdi), %rdi

        /* Indirect call via stack slot - no free GPR to hold the fn ptr. */
        call    *16(%rsp)

        /* Reload output state ptr. %r11 is caller-saved and not tracked
         * by the abicheck, so we use it as scratch. */
        movq    8(%rsp), %r11

        /* Store all GPRs to output state */
        movq    %rdi,   0(%r11)
        movq    %rsi,   8(%r11)
        movq    %rdx,  16(%r11)
        movq    %rcx,  24(%r11)
        movq    %r8,   32(%r11)
        movq    %r9,   40(%r11)
        movq    %rax,  48(%r11)
        movq    %rbx,  56(%r11)
        movq    %rbp,  64(%r11)
        movq    %r12,  72(%r11)
        movq    %r13,  80(%r11)
        movq    %r14,  88(%r11)
        movq    %r15,  96(%r11)
        movq    %r10, 104(%r11)

        /* Epilogue */
        addq    $24, %rsp
        .cfi_adjust_cfa_offset -24
        popq    %rbx
        .cfi_adjust_cfa_offset -8
        .cfi_restore %rbx
        popq    %rbp
        .cfi_adjust_cfa_offset -8
        .cfi_restore %rbp
        popq    %r12
        .cfi_adjust_cfa_offset -8
        .cfi_restore %r12
        popq    %r13
        .cfi_adjust_cfa_offset -8
        .cfi_restore %r13
        popq    %r14
        .cfi_adjust_cfa_offset -8
        .cfi_restore %r14
        popq    %r15
        .cfi_adjust_cfa_offset -8
        .cfi_restore %r15
        ret
        .cfi_endproc
