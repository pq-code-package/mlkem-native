/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../mlkem/src/sys.h"

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

/*
 * Function: asm_call_stub_aarch64
 * Description: AArch64 ABI compliance testing stub that captures register state
 *              before and after function calls to verify AAPCS compliance
 *
 * C Signature: void asm_call_stub_aarch64(struct aarch64_register_state *input,
 *                                         struct aarch64_register_state *output,
 *                                         void (*function_ptr)(void),
 *                                         int use_neon)
 *
 * Stack Usage: 208 bytes total (16-byte aligned)
 *   - 112 bytes for saving callee-saved GPRs (x18-x30: 7 pairs * 16 bytes)
 *   - 64 bytes for saving callee-saved NEON registers (d8-d15: 8 regs * 8 bytes)
 *   - 32 bytes for local variables (output state ptr, function ptr,
 *     use_neon flag, padding)
 */

#define STACK_SIZE_GPRS   112
#define STACK_SIZE_VREGS  64
#define STACK_SIZE_LOCALS 32

#define STACK_SIZE 208
#define STACK_BASE_GPRS 0
#define STACK_BASE_VREGS  STACK_SIZE_GPRS
#define STACK_BASE_LOCALS (STACK_SIZE_GPRS + STACK_SIZE_VREGS)

/* Store \lo,\hi into the (\base, \idx) slot and emit CFI offsets
 * (CFA = sp + STACK_SIZE inside the prologue block). */
.macro save_pair lo, hi, base, idx
        stp \lo, \hi, [sp, #(\base + 16*\idx)]
        .cfi_offset \lo, -(STACK_SIZE - \base - 16*\idx)
        .cfi_offset \hi, -(STACK_SIZE - \base - 16*\idx - 8)
.endm

/* Variant for the (xzr, x18) pair: xzr is filler (no CFI), x18 lives in the
 * upper half of the slot. */
.macro save_pair_padlo hi, base, idx
        stp xzr, \hi, [sp, #(\base + 16*\idx)]
        .cfi_offset \hi, -(STACK_SIZE - \base - 16*\idx - 8)
.endm

/* Reload \lo,\hi from the (\base, \idx) slot and emit CFI restores; the
 * inverse of save_pair. */
.macro restore_pair lo, hi, base, idx
        ldp \lo, \hi, [sp, #(\base + 16*\idx)]
        .cfi_restore \lo
        .cfi_restore \hi
.endm

/* Inverse of save_pair_padlo: reload \hi (xzr discards the filler half), only
 * \hi has CFI. */
.macro restore_pair_padlo hi, base, idx
        ldp xzr, \hi, [sp, #(\base + 16*\idx)]
        .cfi_restore \hi
.endm

/* Callee-saved NEON registers d8-d15. */
#if defined(MLK_SYS_AARCH64_NEON)
.macro save_vregs
        save_pair  d8,  d9, STACK_BASE_VREGS, 0
        save_pair d10, d11, STACK_BASE_VREGS, 1
        save_pair d12, d13, STACK_BASE_VREGS, 2
        save_pair d14, d15, STACK_BASE_VREGS, 3
.endm

.macro restore_vregs
        restore_pair  d8,  d9, STACK_BASE_VREGS, 0
        restore_pair d10, d11, STACK_BASE_VREGS, 1
        restore_pair d12, d13, STACK_BASE_VREGS, 2
        restore_pair d14, d15, STACK_BASE_VREGS, 3
.endm

/* Save the caller's callee-saved vector registers and seed q0-q31 from the
 * input state. Skip every vector instruction when \use_neon is zero. */
.macro save_and_load_vregs use_neon, scratch
        cbz \use_neon, 1f

        save_vregs

        add \scratch, x0,  #256
        ldp q0,  q1,  [\scratch, #(16*0)]
        ldp q2,  q3,  [\scratch, #(16*2)]
        ldp q4,  q5,  [\scratch, #(16*4)]
        ldp q6,  q7,  [\scratch, #(16*6)]
        ldp q8,  q9,  [\scratch, #(16*8)]
        ldp q10, q11, [\scratch, #(16*10)]
        ldp q12, q13, [\scratch, #(16*12)]
        ldp q14, q15, [\scratch, #(16*14)]
        ldp q16, q17, [\scratch, #(16*16)]
        ldp q18, q19, [\scratch, #(16*18)]
        ldp q20, q21, [\scratch, #(16*20)]
        ldp q22, q23, [\scratch, #(16*22)]
        ldp q24, q25, [\scratch, #(16*24)]
        ldp q26, q27, [\scratch, #(16*26)]
        ldp q28, q29, [\scratch, #(16*28)]
        ldp q30, q31, [\scratch, #(16*30)]

1:
.endm

/* Capture q0-q31 in the output state and restore the caller's callee-saved
 * vector registers. Skip every vector instruction when \use_neon is zero. */
.macro store_and_restore_vregs use_neon, scratch
        ldr \use_neon, [sp, #(STACK_BASE_LOCALS + 16)]
        cbz \use_neon, 1f

        ldr \scratch, [sp, #(STACK_BASE_LOCALS + 0)]
        add \scratch, \scratch, #256
        stp q0,  q1,  [\scratch, #(16*0)]
        stp q2,  q3,  [\scratch, #(16*2)]
        stp q4,  q5,  [\scratch, #(16*4)]
        stp q6,  q7,  [\scratch, #(16*6)]
        stp q8,  q9,  [\scratch, #(16*8)]
        stp q10, q11, [\scratch, #(16*10)]
        stp q12, q13, [\scratch, #(16*12)]
        stp q14, q15, [\scratch, #(16*14)]
        stp q16, q17, [\scratch, #(16*16)]
        stp q18, q19, [\scratch, #(16*18)]
        stp q20, q21, [\scratch, #(16*20)]
        stp q22, q23, [\scratch, #(16*22)]
        stp q24, q25, [\scratch, #(16*24)]
        stp q26, q27, [\scratch, #(16*26)]
        stp q28, q29, [\scratch, #(16*28)]
        stp q30, q31, [\scratch, #(16*30)]

        restore_vregs

1:
.endm
#else /* MLK_SYS_AARCH64_NEON */
.macro save_and_load_vregs use_neon, scratch
.endm

.macro store_and_restore_vregs use_neon, scratch
.endm
#endif /* !MLK_SYS_AARCH64_NEON */

/* Save the caller's callee-saved GPRs and seed x0-x29 from the input state
 * initially passed in x0. xzr pads the x18 slot for 16-byte alignment. */
.macro save_and_load_gprs
        save_pair_padlo x18, STACK_BASE_GPRS, 0
        save_pair x19, x20, STACK_BASE_GPRS, 1
        save_pair x21, x22, STACK_BASE_GPRS, 2
        save_pair x23, x24, STACK_BASE_GPRS, 3
        save_pair x25, x26, STACK_BASE_GPRS, 4
        save_pair x27, x28, STACK_BASE_GPRS, 5
        save_pair x29, x30, STACK_BASE_GPRS, 6

        mov x30, x0
        ldp x0,  x1,  [x30, #(8*0)]
        ldp x2,  x3,  [x30, #(8*2)]
        ldp x4,  x5,  [x30, #(8*4)]
        ldp x6,  x7,  [x30, #(8*6)]
        ldp x8,  x9,  [x30, #(8*8)]
        ldp x10, x11, [x30, #(8*10)]
        ldp x12, x13, [x30, #(8*12)]
        ldp x14, x15, [x30, #(8*14)]
        ldp x16, x17, [x30, #(8*16)]
#ifdef __APPLE__
        /* x18 is the platform register on Darwin and reserved by the OS;
         * user code must not clobber it. Skip seeding x18 from the random
         * input state, and instead overwrite input->gpr[18] with the live
         * x18 value so the post-call comparison still has a meaningful
         * pre-call baseline (the kernel under test must leave x18
         * unchanged either way). */
        str x18, [x30, #(8*18)]
        ldr x19, [x30, #(8*19)]
#else /* __APPLE__ */
        ldp x18, x19, [x30, #(8*18)]
#endif /* !__APPLE__ */
        ldp x20, x21, [x30, #(8*20)]
        ldp x22, x23, [x30, #(8*22)]
        ldp x24, x25, [x30, #(8*24)]
        ldp x26, x27, [x30, #(8*26)]
        ldp x28, x29, [x30, #(8*28)]
.endm

/* Capture x0-x29 in the output state and restore the caller's callee-saved
 * GPRs. */
.macro store_and_restore_gprs
        ldr x30, [sp, #(STACK_BASE_LOCALS + 0)]

        stp x0,  x1,  [x30, #(8*0)]
        stp x2,  x3,  [x30, #(8*2)]
        stp x4,  x5,  [x30, #(8*4)]
        stp x6,  x7,  [x30, #(8*6)]
        stp x8,  x9,  [x30, #(8*8)]
        stp x10, x11, [x30, #(8*10)]
        stp x12, x13, [x30, #(8*12)]
        stp x14, x15, [x30, #(8*14)]
        stp x16, x17, [x30, #(8*16)]
        stp x18, x19, [x30, #(8*18)]
        stp x20, x21, [x30, #(8*20)]
        stp x22, x23, [x30, #(8*22)]
        stp x24, x25, [x30, #(8*24)]
        stp x26, x27, [x30, #(8*26)]
        stp x28, x29, [x30, #(8*28)]

        restore_pair_padlo x18, STACK_BASE_GPRS, 0
        restore_pair x19, x20, STACK_BASE_GPRS, 1
        restore_pair x21, x22, STACK_BASE_GPRS, 2
        restore_pair x23, x24, STACK_BASE_GPRS, 3
        restore_pair x25, x26, STACK_BASE_GPRS, 4
        restore_pair x27, x28, STACK_BASE_GPRS, 5
        restore_pair x29, x30, STACK_BASE_GPRS, 6
.endm

.text
.balign 4
#ifdef __APPLE__
.global _asm_call_stub_aarch64
_asm_call_stub_aarch64:
#else
.global asm_call_stub_aarch64
asm_call_stub_aarch64:
#endif
        .cfi_startproc
        sub sp, sp, #(STACK_SIZE)
        .cfi_def_cfa_offset STACK_SIZE

        /* Spill output ptr (x1), fn ptr (x2), and use_neon (w3). */
        stp x1, x2, [sp, #(STACK_BASE_LOCALS)]
        str w3, [sp, #(STACK_BASE_LOCALS + 16)]

        save_and_load_vregs w3, x3
        save_and_load_gprs

        ldr x30, [sp, #(STACK_BASE_LOCALS + 8)]
        blr x30

        store_and_restore_gprs
        store_and_restore_vregs w3, x3
        add sp, sp, #(STACK_SIZE)
        .cfi_def_cfa_offset 0
        ret
        .cfi_endproc
