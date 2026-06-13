/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

/*
 * Function: asm_call_stub_armv81m
 * Description: Armv8.1-M (Thumb-2, AAPCS32) ABI compliance testing stub.
 *              Captures the full GPR / MVE register state before and after a
 *              call to verify the callee preserves the AAPCS32 callee-saved
 *              set.
 *
 * C signature:
 *   void asm_call_stub_armv81m(struct armv81m_register_state *input,
 *                              struct armv81m_register_state *output,
 *                              void (*function_ptr)(void));
 *
 * AAPCS32 callee-saved registers we preserve for our own caller:
 *   - r4-r11
 *   - lr (we use it ourselves, save/restore via push/pop)
 *   - Q4-Q7 (= D8-D15)
 * (r12 is caller-saved (IP); r13 is sp; we never touch r13 except for stack
 * management.)
 *
 * All of r0-r12 are seeded from input->gpr[]: the kernel itself decides
 * which of r0-r3 are arguments and which of r4-r11 it must preserve, so
 * the stub seeds every register and lets the C side check what AAPCS32
 * actually required.
 *
 * Stack layout once the prologue is complete:
 *
 *   sp +   0: output_ptr   (push {r1, r2})
 *   sp +   4: function_ptr (push {r1, r2})
 *   sp +   8..71  : d8..d15            (vpush {d8-d15})
 *   sp +  72..111 : r4..r12, lr        (push {r4-r12, lr})
 *
 * After the inner blx, before we restore our own state, we additionally
 * spill r0-r12 with stmdb to free a scratch register for the output stores.
 */

#define LOC_OUTPUT_PTR   0
#define LOC_FUNCTION_PTR 4
#define LOCALS_SIZE      8

/* Offset of mve[] inside struct armv81m_register_state. Must stay in sync
 * with abicheckutil.h. */
#define STATE_MVE_OFFSET 64

/* Width in bytes of the post-blx `stmdb sp!, {r0-r12}` spill (13 GPRs * 4).
 * After that spill the original locals at sp+LOC_* are this much further down
 * the stack, so we re-read output_ptr at sp+(52 + LOC_OUTPUT_PTR). */
#define LOCALS_OFFSET_AFTER_GPR_SPILL  (52 + LOC_OUTPUT_PTR)

.text
.balign 4
.thumb
.syntax unified
.global asm_call_stub_armv81m
.type asm_call_stub_armv81m, %function
asm_call_stub_armv81m:
        .cfi_startproc
        /* --- Prologue: save our own callee-saved registers and stash args --- */
        push    {r4-r12, lr}
        .cfi_adjust_cfa_offset 40
        .cfi_offset r4,  -40
        .cfi_offset r5,  -36
        .cfi_offset r6,  -32
        .cfi_offset r7,  -28
        .cfi_offset r8,  -24
        .cfi_offset r9,  -20
        .cfi_offset r10, -16
        .cfi_offset r11, -12
        .cfi_offset r12, -8
        .cfi_offset lr,  -4
        vpush   {d8-d15}
        .cfi_adjust_cfa_offset 64
        push    {r1, r2}              /* output_ptr at sp+0, function_ptr at sp+4 */
        .cfi_adjust_cfa_offset 8

        /* --- Load Q0-Q7 from input->mve[] --- */
        /* r1 already saved on the stack, free to clobber. */
        add     r1, r0, #STATE_MVE_OFFSET
        vldrw.u32 q0, [r1, #(0 * 16)]
        vldrw.u32 q1, [r1, #(1 * 16)]
        vldrw.u32 q2, [r1, #(2 * 16)]
        vldrw.u32 q3, [r1, #(3 * 16)]
        vldrw.u32 q4, [r1, #(4 * 16)]
        vldrw.u32 q5, [r1, #(5 * 16)]
        vldrw.u32 q6, [r1, #(6 * 16)]
        vldrw.u32 q7, [r1, #(7 * 16)]

        /* --- Load r0-r12 from input->gpr[] --- */
        /* r0 is currently the input-state pointer; load r1..r12 via offset
         * addressing relative to r0, then overwrite r0 itself last. We avoid
         * `ldm rN, {rN, ...}` because Thumb-2 deprecates having the base in
         * the register list without writeback. */
        ldr     r1,  [r0, #( 1 * 4)]
        ldr     r2,  [r0, #( 2 * 4)]
        ldr     r3,  [r0, #( 3 * 4)]
        ldr     r4,  [r0, #( 4 * 4)]
        ldr     r5,  [r0, #( 5 * 4)]
        ldr     r6,  [r0, #( 6 * 4)]
        ldr     r7,  [r0, #( 7 * 4)]
        ldr     r8,  [r0, #( 8 * 4)]
        ldr     r9,  [r0, #( 9 * 4)]
        ldr     r10, [r0, #(10 * 4)]
        ldr     r11, [r0, #(11 * 4)]
        ldr     r12, [r0, #(12 * 4)]
        ldr     r0,  [r0, #( 0 * 4)]  /* r0 last (overwrites the base) */

        /* --- Recover function_ptr and call. r12 (IP, caller-saved) is OK to
         * clobber here even though we just loaded it: the AAPCS32 contract
         * does not require r12 to be preserved. --- */
        ldr     r12, [sp, #LOC_FUNCTION_PTR]
        blx     r12

        /* --- Capture post-call state: dump r0-r12 and Q0-Q7. The C side
         * compares the AAPCS32 callee-saved subset (r4-r11, Q4-Q7). --- */

        /* Spill r0-r12 to free a scratch register. After this stmdb the
         * captured values live at [sp+0..48], in slot order r0..r12. */
        stmdb   sp!, {r0-r12}
        .cfi_adjust_cfa_offset 52

        /* Output pointer location was at sp + LOC_OUTPUT_PTR; the spill
         * above shifted everything by 52 bytes. */
        ldr     r0, [sp, #LOCALS_OFFSET_AFTER_GPR_SPILL]

        /* Copy r0..r12 from the spill area to output->gpr[0..12]. r1 is the
         * only scratch we have; r0 holds output_ptr. Unrolled ldr/str pairs. */
        ldr     r1, [sp, #(0 * 4)]    /* captured r0  */
        str     r1, [r0, #(0 * 4)]
        ldr     r1, [sp, #(1 * 4)]    /* captured r1  */
        str     r1, [r0, #(1 * 4)]
        ldr     r1, [sp, #(2 * 4)]    /* captured r2  */
        str     r1, [r0, #(2 * 4)]
        ldr     r1, [sp, #(3 * 4)]    /* captured r3  */
        str     r1, [r0, #(3 * 4)]
        ldr     r1, [sp, #(4 * 4)]    /* captured r4  */
        str     r1, [r0, #(4 * 4)]
        ldr     r1, [sp, #(5 * 4)]    /* captured r5  */
        str     r1, [r0, #(5 * 4)]
        ldr     r1, [sp, #(6 * 4)]    /* captured r6  */
        str     r1, [r0, #(6 * 4)]
        ldr     r1, [sp, #(7 * 4)]    /* captured r7  */
        str     r1, [r0, #(7 * 4)]
        ldr     r1, [sp, #(8 * 4)]    /* captured r8  */
        str     r1, [r0, #(8 * 4)]
        ldr     r1, [sp, #(9 * 4)]    /* captured r9  */
        str     r1, [r0, #(9 * 4)]
        ldr     r1, [sp, #(10 * 4)]   /* captured r10 */
        str     r1, [r0, #(10 * 4)]
        ldr     r1, [sp, #(11 * 4)]   /* captured r11 */
        str     r1, [r0, #(11 * 4)]
        ldr     r1, [sp, #(12 * 4)]   /* captured r12 */
        str     r1, [r0, #(12 * 4)]

        /* Drop the GPR spill area. */
        add     sp, sp, #52
        .cfi_adjust_cfa_offset -52

        /* --- Capture Q0-Q7 into output->mve[]. --- */
        add     r1, r0, #STATE_MVE_OFFSET
        vstrw.32 q0, [r1, #(0 * 16)]
        vstrw.32 q1, [r1, #(1 * 16)]
        vstrw.32 q2, [r1, #(2 * 16)]
        vstrw.32 q3, [r1, #(3 * 16)]
        vstrw.32 q4, [r1, #(4 * 16)]
        vstrw.32 q5, [r1, #(5 * 16)]
        vstrw.32 q6, [r1, #(6 * 16)]
        vstrw.32 q7, [r1, #(7 * 16)]

        /* --- Epilogue: restore our own callee-saves and return. --- */
        add     sp, sp, #LOCALS_SIZE  /* drop output_ptr/function_ptr locals */
        .cfi_adjust_cfa_offset -8
        vpop    {d8-d15}
        .cfi_adjust_cfa_offset -64
        pop     {r4-r12, pc}
        .cfi_endproc
