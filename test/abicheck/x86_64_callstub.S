/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../mlkem/src/sys.h"
#if defined(MLK_SYS_X86_64)

/*
 * Function: asm_call_stub_x86_64
 * Description: x86_64 System V ABI compliance testing stub
 *
 * C Signature: void asm_call_stub_x86_64(
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
 * Stack layout after prologue (16-byte aligned):
 *   [rsp+0]:  output state ptr
 *   [rsp+8]:  function ptr
 *   [rsp+16]: saved rbx
 *   [rsp+24]: saved rbp
 *   [rsp+32]: saved r12
 *   [rsp+40]: saved r13
 *   [rsp+48]: saved r14
 *   [rsp+56]: saved r15
 *   [rsp+64]: (alignment pad / return address area)
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 16
#ifdef __APPLE__
.global _asm_call_stub_x86_64
_asm_call_stub_x86_64:
#else
.global asm_call_stub_x86_64
asm_call_stub_x86_64:
#endif
        .cfi_startproc
        /* Save callee-saved registers */
        pushq   %r15
        pushq   %r14
        pushq   %r13
        pushq   %r12
        pushq   %rbp
        pushq   %rbx

        /* Reserve space for output ptr + function ptr */
        subq    $16, %rsp

        /* Save output state ptr and function ptr to stack */
        movq    %rsi, 0(%rsp)   /* output state ptr */
        movq    %rdx, 8(%rsp)   /* function ptr */

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

        /* Call target function via stack-saved pointer.
         * We use call *offset(%rsp) to avoid clobbering any register. */
        call    *8(%rsp)

        /* Now save output register state.
         * Load output state ptr - we need a scratch register.
         * r11 is caller-saved and not checked, so we use it here.
         * This means r11's post-call value is not captured in the
         * output state, which is fine since it's not callee-saved. */
        movq    0(%rsp), %r11

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
        addq    $16, %rsp
        popq    %rbx
        popq    %rbp
        popq    %r12
        popq    %r13
        popq    %r14
        popq    %r15
        ret
        .cfi_endproc

#endif /* MLK_SYS_X86_64 */
