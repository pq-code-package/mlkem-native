/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../mlkem/src/sys.h"
#if defined(MLK_SYS_PPC64LE)

/*
 * Function: asm_call_stub_ppc64le
 * Description: PowerPC64 ELF v2 ABI compliance testing stub.
 *
 * C signature:
 *   void asm_call_stub_ppc64le(
 *       struct ppc64le_register_state *input,    // r3
 *       struct ppc64le_register_state *output,   // r4
 *       void (*function_ptr)(void))              // r5
 *
 * It loads the full register state from *input, calls function_ptr, and
 * captures the resulting register state into *output. It does NOT assume
 * function_ptr obeys the calling convention - that is what we are testing -
 * so it is written in assembly and saves/restores its own non-volatiles.
 *
 * struct ppc64le_register_state layout (matches abicheckutil.h):
 *   offset   0: gpr_arg[8]  r3-r10        (8  * 8  = 64 bytes)
 *   offset  64: gpr_nv[18]  r14-r31       (18 * 8  = 144 bytes)
 *   offset 208: fpr[18]     f14-f31       (18 * 8  = 144 bytes)
 *   offset 352: vr[12][2]   v20-v31       (12 * 16 = 192 bytes)
 *   offset 544: cr          condition reg (8 bytes)
 *
 * ELF v2 non-volatile (callee-saved) registers: r14-r31, f14-f31, v20-v31,
 * CR2-CR4, and LR.
 */

#define ST_GPR_ARG 0   /* r3-r10            */
#define ST_GPR_NV 64   /* r14-r31           */
#define ST_FPR 208     /* f14-f31           */
#define ST_VR 352      /* v20-v31           */
#define ST_CR 544      /* condition register */

/*
 * Our own stack frame. We must preserve every non-volatile we touch:
 *   - r14-r31      (we use several as scratch while marshalling state)
 *   - f14-f31      (loaded from / stored to the state)
 *   - v20-v31      (loaded from / stored to the state)
 *   - CR2-CR4, LR  (clobbered by the call / our own control flow)
 * We also stash the input/output/function pointers across the call.
 *
 * Frame layout (offsets from our r1 after stdu), 16-byte aligned:
 *   0                : back-chain (set by stdu)
 *   FRAME_PTRS  (16) : saved input ptr, output ptr, function ptr (3 * 8)
 *   FRAME_GPR   (48) : saved r14-r31         (18 * 8 = 144)
 *   FRAME_FPR  (192) : saved f14-f31         (18 * 8 = 144)
 *   FRAME_CR   (336) : saved CR              (8)
 *   FRAME_VR   (352) : saved v20-v31, 16-aligned (12 * 16 = 192)
 *   total      (544) -> round up to 16:  544 is a multiple of 16.
 */
#define FRAME_PTRS 16
#define FRAME_GPR 48
#define FRAME_FPR 192
#define FRAME_CR 336
#define FRAME_VR 352
#define FRAME_SIZE 544

.text
.abiversion 2
.balign 4
.global asm_call_stub_ppc64le
.type asm_call_stub_ppc64le, @function

asm_call_stub_ppc64le:
0:
        addis   2, 12, (.TOC. - 0b)@ha
        addi    2, 2, (.TOC. - 0b)@l
        .localentry asm_call_stub_ppc64le, . - 0b

        .cfi_startproc
        mflr    0
        std     0, 16(1)              /* save LR into caller frame */
        stdu    1, -FRAME_SIZE(1)     /* allocate our frame */

        /* Save the three pointer arguments */
        std     3, FRAME_PTRS+0(1)    /* input  */
        std     4, FRAME_PTRS+8(1)    /* output */
        std     5, FRAME_PTRS+16(1)   /* function_ptr */

        /* --- Save our own non-volatile GPRs r14-r31 --- */
        std     14, FRAME_GPR+0(1)
        std     15, FRAME_GPR+8(1)
        std     16, FRAME_GPR+16(1)
        std     17, FRAME_GPR+24(1)
        std     18, FRAME_GPR+32(1)
        std     19, FRAME_GPR+40(1)
        std     20, FRAME_GPR+48(1)
        std     21, FRAME_GPR+56(1)
        std     22, FRAME_GPR+64(1)
        std     23, FRAME_GPR+72(1)
        std     24, FRAME_GPR+80(1)
        std     25, FRAME_GPR+88(1)
        std     26, FRAME_GPR+96(1)
        std     27, FRAME_GPR+104(1)
        std     28, FRAME_GPR+112(1)
        std     29, FRAME_GPR+120(1)
        std     30, FRAME_GPR+128(1)
        std     31, FRAME_GPR+136(1)

        /* --- Save our own non-volatile FPRs f14-f31 --- */
        stfd    14, FRAME_FPR+0(1)
        stfd    15, FRAME_FPR+8(1)
        stfd    16, FRAME_FPR+16(1)
        stfd    17, FRAME_FPR+24(1)
        stfd    18, FRAME_FPR+32(1)
        stfd    19, FRAME_FPR+40(1)
        stfd    20, FRAME_FPR+48(1)
        stfd    21, FRAME_FPR+56(1)
        stfd    22, FRAME_FPR+64(1)
        stfd    23, FRAME_FPR+72(1)
        stfd    24, FRAME_FPR+80(1)
        stfd    25, FRAME_FPR+88(1)
        stfd    26, FRAME_FPR+96(1)
        stfd    27, FRAME_FPR+104(1)
        stfd    28, FRAME_FPR+112(1)
        stfd    29, FRAME_FPR+120(1)
        stfd    30, FRAME_FPR+128(1)
        stfd    31, FRAME_FPR+136(1)

        /* --- Save our own non-volatile CR fields --- */
        mfcr    0
        stw     0, FRAME_CR(1)

        /* --- Save our own non-volatile VRs v20-v31 --- */
        li      9, FRAME_VR
        stvx    20, 1, 9
        addi    9, 9, 16
        stvx    21, 1, 9
        addi    9, 9, 16
        stvx    22, 1, 9
        addi    9, 9, 16
        stvx    23, 1, 9
        addi    9, 9, 16
        stvx    24, 1, 9
        addi    9, 9, 16
        stvx    25, 1, 9
        addi    9, 9, 16
        stvx    26, 1, 9
        addi    9, 9, 16
        stvx    27, 1, 9
        addi    9, 9, 16
        stvx    28, 1, 9
        addi    9, 9, 16
        stvx    29, 1, 9
        addi    9, 9, 16
        stvx    30, 1, 9
        addi    9, 9, 16
        stvx    31, 1, 9

        /*
         * Load the input register state. We use r31 as the base pointer to the
         * input struct while loading, because the input value of r31 itself
         * comes from the state and is loaded last.
         */
        mr      31, 3                 /* r31 = input ptr */

        /* Load non-volatile FPRs f14-f31 from state */
        lfd     14, ST_FPR+0(31)
        lfd     15, ST_FPR+8(31)
        lfd     16, ST_FPR+16(31)
        lfd     17, ST_FPR+24(31)
        lfd     18, ST_FPR+32(31)
        lfd     19, ST_FPR+40(31)
        lfd     20, ST_FPR+48(31)
        lfd     21, ST_FPR+56(31)
        lfd     22, ST_FPR+64(31)
        lfd     23, ST_FPR+72(31)
        lfd     24, ST_FPR+80(31)
        lfd     25, ST_FPR+88(31)
        lfd     26, ST_FPR+96(31)
        lfd     27, ST_FPR+104(31)
        lfd     28, ST_FPR+112(31)
        lfd     29, ST_FPR+120(31)
        lfd     30, ST_FPR+128(31)
        lfd     31, ST_FPR+136(31)

        /* Load non-volatile VRs v20-v31 from state */
        li      9, ST_VR
        lvx     20, 31, 9
        addi    9, 9, 16
        lvx     21, 31, 9
        addi    9, 9, 16
        lvx     22, 31, 9
        addi    9, 9, 16
        lvx     23, 31, 9
        addi    9, 9, 16
        lvx     24, 31, 9
        addi    9, 9, 16
        lvx     25, 31, 9
        addi    9, 9, 16
        lvx     26, 31, 9
        addi    9, 9, 16
        lvx     27, 31, 9
        addi    9, 9, 16
        lvx     28, 31, 9
        addi    9, 9, 16
        lvx     29, 31, 9
        addi    9, 9, 16
        lvx     30, 31, 9
        addi    9, 9, 16
        lvx     31, 31, 9

        /* Load condition register fields from state */
        lwz     0, ST_CR(31)
        mtcr    0

        /* Set up the call target in CTR and r12 (ELF v2 global-entry needs r12
         * = entry point). function_ptr was saved on the stack. */
        ld      12, FRAME_PTRS+16(1)
        mtctr   12

        /*
         * Load the argument GPRs r3-r10 from state. After this, r3-r10 hold the
         * caller-supplied argument values and r31 still points at input.
         */
        ld      3, ST_GPR_ARG+0(31)
        ld      4, ST_GPR_ARG+8(31)
        ld      5, ST_GPR_ARG+16(31)
        ld      6, ST_GPR_ARG+24(31)
        ld      7, ST_GPR_ARG+32(31)
        ld      8, ST_GPR_ARG+40(31)
        ld      9, ST_GPR_ARG+48(31)
        ld      10, ST_GPR_ARG+56(31)

        /* Load the non-volatile GPRs r14-r31 from state (r31 last). */
        ld      14, ST_GPR_NV+0(31)
        ld      15, ST_GPR_NV+8(31)
        ld      16, ST_GPR_NV+16(31)
        ld      17, ST_GPR_NV+24(31)
        ld      18, ST_GPR_NV+32(31)
        ld      19, ST_GPR_NV+40(31)
        ld      20, ST_GPR_NV+48(31)
        ld      21, ST_GPR_NV+56(31)
        ld      22, ST_GPR_NV+64(31)
        ld      23, ST_GPR_NV+72(31)
        ld      24, ST_GPR_NV+80(31)
        ld      25, ST_GPR_NV+88(31)
        ld      26, ST_GPR_NV+96(31)
        ld      27, ST_GPR_NV+104(31)
        ld      28, ST_GPR_NV+112(31)
        ld      29, ST_GPR_NV+120(31)
        ld      30, ST_GPR_NV+128(31)
        ld      31, ST_GPR_NV+136(31)

        /* Call the function under test. */
        bctrl

        /*
         * Capture the resulting register state. r3-r12 are volatile and were
         * clobbered by the call, so we may freely use them. Reload the output
         * pointer into r12.
         */
        ld      12, FRAME_PTRS+8(1)   /* r12 = output ptr */

        /* Store non-volatile GPRs r14-r31 to output. */
        std     14, ST_GPR_NV+0(12)
        std     15, ST_GPR_NV+8(12)
        std     16, ST_GPR_NV+16(12)
        std     17, ST_GPR_NV+24(12)
        std     18, ST_GPR_NV+32(12)
        std     19, ST_GPR_NV+40(12)
        std     20, ST_GPR_NV+48(12)
        std     21, ST_GPR_NV+56(12)
        std     22, ST_GPR_NV+64(12)
        std     23, ST_GPR_NV+72(12)
        std     24, ST_GPR_NV+80(12)
        std     25, ST_GPR_NV+88(12)
        std     26, ST_GPR_NV+96(12)
        std     27, ST_GPR_NV+104(12)
        std     28, ST_GPR_NV+112(12)
        std     29, ST_GPR_NV+120(12)
        std     30, ST_GPR_NV+128(12)
        std     31, ST_GPR_NV+136(12)

        /* Store the argument GPRs r3-r10 to output (post-call values). */
        std     3, ST_GPR_ARG+0(12)
        std     4, ST_GPR_ARG+8(12)
        std     5, ST_GPR_ARG+16(12)
        std     6, ST_GPR_ARG+24(12)
        std     7, ST_GPR_ARG+32(12)
        std     8, ST_GPR_ARG+40(12)
        std     9, ST_GPR_ARG+48(12)
        std     10, ST_GPR_ARG+56(12)

        /* Store non-volatile FPRs f14-f31 to output. */
        stfd    14, ST_FPR+0(12)
        stfd    15, ST_FPR+8(12)
        stfd    16, ST_FPR+16(12)
        stfd    17, ST_FPR+24(12)
        stfd    18, ST_FPR+32(12)
        stfd    19, ST_FPR+40(12)
        stfd    20, ST_FPR+48(12)
        stfd    21, ST_FPR+56(12)
        stfd    22, ST_FPR+64(12)
        stfd    23, ST_FPR+72(12)
        stfd    24, ST_FPR+80(12)
        stfd    25, ST_FPR+88(12)
        stfd    26, ST_FPR+96(12)
        stfd    27, ST_FPR+104(12)
        stfd    28, ST_FPR+112(12)
        stfd    29, ST_FPR+120(12)
        stfd    30, ST_FPR+128(12)
        stfd    31, ST_FPR+136(12)

        /* Store non-volatile VRs v20-v31 to output. */
        li      9, ST_VR
        stvx    20, 12, 9
        addi    9, 9, 16
        stvx    21, 12, 9
        addi    9, 9, 16
        stvx    22, 12, 9
        addi    9, 9, 16
        stvx    23, 12, 9
        addi    9, 9, 16
        stvx    24, 12, 9
        addi    9, 9, 16
        stvx    25, 12, 9
        addi    9, 9, 16
        stvx    26, 12, 9
        addi    9, 9, 16
        stvx    27, 12, 9
        addi    9, 9, 16
        stvx    28, 12, 9
        addi    9, 9, 16
        stvx    29, 12, 9
        addi    9, 9, 16
        stvx    30, 12, 9
        addi    9, 9, 16
        stvx    31, 12, 9

        /* Store the condition register to output. */
        mfcr    0
        stw     0, ST_CR(12)

        /* --- Restore our own non-volatile state --- */
        /* VRs */
        li      9, FRAME_VR
        lvx     20, 1, 9
        addi    9, 9, 16
        lvx     21, 1, 9
        addi    9, 9, 16
        lvx     22, 1, 9
        addi    9, 9, 16
        lvx     23, 1, 9
        addi    9, 9, 16
        lvx     24, 1, 9
        addi    9, 9, 16
        lvx     25, 1, 9
        addi    9, 9, 16
        lvx     26, 1, 9
        addi    9, 9, 16
        lvx     27, 1, 9
        addi    9, 9, 16
        lvx     28, 1, 9
        addi    9, 9, 16
        lvx     29, 1, 9
        addi    9, 9, 16
        lvx     30, 1, 9
        addi    9, 9, 16
        lvx     31, 1, 9

        /* CR */
        lwz     0, FRAME_CR(1)
        mtcr    0

        /* FPRs */
        lfd     14, FRAME_FPR+0(1)
        lfd     15, FRAME_FPR+8(1)
        lfd     16, FRAME_FPR+16(1)
        lfd     17, FRAME_FPR+24(1)
        lfd     18, FRAME_FPR+32(1)
        lfd     19, FRAME_FPR+40(1)
        lfd     20, FRAME_FPR+48(1)
        lfd     21, FRAME_FPR+56(1)
        lfd     22, FRAME_FPR+64(1)
        lfd     23, FRAME_FPR+72(1)
        lfd     24, FRAME_FPR+80(1)
        lfd     25, FRAME_FPR+88(1)
        lfd     26, FRAME_FPR+96(1)
        lfd     27, FRAME_FPR+104(1)
        lfd     28, FRAME_FPR+112(1)
        lfd     29, FRAME_FPR+120(1)
        lfd     30, FRAME_FPR+128(1)
        lfd     31, FRAME_FPR+136(1)

        /* GPRs */
        ld      14, FRAME_GPR+0(1)
        ld      15, FRAME_GPR+8(1)
        ld      16, FRAME_GPR+16(1)
        ld      17, FRAME_GPR+24(1)
        ld      18, FRAME_GPR+32(1)
        ld      19, FRAME_GPR+40(1)
        ld      20, FRAME_GPR+48(1)
        ld      21, FRAME_GPR+56(1)
        ld      22, FRAME_GPR+64(1)
        ld      23, FRAME_GPR+72(1)
        ld      24, FRAME_GPR+80(1)
        ld      25, FRAME_GPR+88(1)
        ld      26, FRAME_GPR+96(1)
        ld      27, FRAME_GPR+104(1)
        ld      28, FRAME_GPR+112(1)
        ld      29, FRAME_GPR+120(1)
        ld      30, FRAME_GPR+128(1)
        ld      31, FRAME_GPR+136(1)

        /* Tear down frame and return. */
        addi    1, 1, FRAME_SIZE
        ld      0, 16(1)
        mtlr    0
        blr
        .cfi_endproc
.size asm_call_stub_ppc64le, . - asm_call_stub_ppc64le

#if defined(__ELF__)
.section .note.GNU-stack, "", @progbits
#endif

#endif /* MLK_SYS_PPC64LE */
