/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Bare-metal startup for AArch64 QEMU virt machine.
 *
 * - Exception vector table (reports faults via semihosting and exits)
 * - EL2 -> EL1 drop (QEMU virt boots at EL2)
 * - Stack setup
 * - Enable Advanced SIMD/NEON (CPACR_EL1.FPEN)
 * - Call main
 * - Semihosting exit on return
 */

    .section .text.vectors, "ax"
    .balign 2048
vectors:
    /* Current EL with SP0 */
    .balign 128
    b   _start              /* Synchronous   */
    .balign 128
    b   unhandled_exception /* IRQ           */
    .balign 128
    b   unhandled_exception /* FIQ           */
    .balign 128
    b   unhandled_exception /* SError        */

    /* Current EL with SPx */
    .balign 128
    b   sync_handler        /* Synchronous   */
    .balign 128
    b   unhandled_exception /* IRQ           */
    .balign 128
    b   unhandled_exception /* FIQ           */
    .balign 128
    b   unhandled_exception /* SError        */

    /* Lower EL using AArch64 */
    .balign 128
    b   unhandled_exception
    .balign 128
    b   unhandled_exception
    .balign 128
    b   unhandled_exception
    .balign 128
    b   unhandled_exception

    /* Lower EL using AArch32 */
    .balign 128
    b   unhandled_exception
    .balign 128
    b   unhandled_exception
    .balign 128
    b   unhandled_exception
    .balign 128
    b   unhandled_exception

/*
 * Synchronous exception handler.
 * Uses a dedicated stack to avoid recursive faults.
 */
sync_handler:
    adrp x0, __exc_stack_top
    add  x0, x0, :lo12:__exc_stack_top
    mov  sp, x0

    mrs x0, esr_el1
    mrs x1, elr_el1
    mrs x2, far_el1
    bl  report_exception
    mov x1, #1
    b   semihosting_exit

/*
 * Unhandled exception: just exit with failure.
 */
unhandled_exception:
    mov x1, #1
    b   semihosting_exit

    .section .text.start, "ax"
    .globl _start
_start:
    /* Check current exception level */
    mrs x0, CurrentEL
    lsr x0, x0, #2
    cmp x0, #2
    b.ne 1f

    /* --- Running at EL2: drop to EL1 --- */

    /* EL1 is AArch64 */
    mov x0, #(1 << 31)         /* HCR_EL2.RW = 1 (AArch64 at EL1) */
    msr hcr_el2, x0

    /* SPSR_EL2: DAIF masked, EL1h */
    mov x0, #0x3c5
    msr spsr_el2, x0

    /* Return to el1_entry */
    adr x0, 1f
    msr elr_el2, x0
    eret

1:
    /* --- Now at EL1 --- */

    /* Set up the vector table */
    adrp x0, vectors
    add  x0, x0, :lo12:vectors
    msr vbar_el1, x0
    isb

    /* Enable Advanced SIMD and FP (CPACR_EL1.FPEN = 0b11) */
    mov x0, #(3 << 20)
    msr cpacr_el1, x0
    isb

    /* Set up the stack */
    adrp x0, __stack_top
    add  x0, x0, :lo12:__stack_top
    mov sp, x0

    /* Clear BSS */
    adrp x0, __bss_start
    add  x0, x0, :lo12:__bss_start
    adrp x1, __bss_end
    add  x1, x1, :lo12:__bss_end
2:
    cmp x0, x1
    b.ge 3f
    str xzr, [x0], #8
    b   2b
3:

    /* Call _start_c() which parses cmdline and calls main */
    bl  _start_c

    /* _start_c should not return, but if it does, exit */
    mov x1, x0
    b   semihosting_exit

/*
 * Semihosting exit.
 * x1 = exit code (0 = success, nonzero = failure)
 */
    .globl semihosting_exit
semihosting_exit:
    /*
     * AArch64 semihosting: SYS_EXIT_EXTENDED (0x20)
     * Parameter block: [field1=ADP_Stopped_ApplicationExit, field2=exit_code]
     */
    stp x1, xzr, [sp, #-16]!
    movz x0, #0x0002, lsl #16  /* ADP_Stopped_ApplicationExit = 0x20026 */
    movk x0, #0x0026
    str x0, [sp]
    str x1, [sp, #8]
    mov x1, sp
    mov w0, #0x20               /* SYS_EXIT_EXTENDED */
    hlt #0xf000
    /* Should not return */
4:
    wfe
    b   4b
