/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../mlkem/src/sys.h"

#if defined(MLK_SYS_RISCV64)

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

/*
 * Function: asm_call_stub_riscv64
 * Description: RISC-V 64 ABI compliance testing stub that captures register
 *              state before and after function calls to verify LP64D
 *              compliance
 *
 * C Signature: void asm_call_stub_riscv64(struct riscv64_register_state *input,
 *                                         struct riscv64_register_state *output,
 *                                         void (*function_ptr)(void))
 *
 * Register state layout: gpr[32] at offset 0, fpr[32] at offset 256.
 *
 * All GPRs except ra, sp, gp and tp are seeded from the input state. gp and
 * tp are reserved for the platform: their live values are written back to
 * the input state as the baseline instead. FPRs are seeded only for the
 * LP64D ABI.
 *
 * Stack Usage: 224 bytes total (16-byte aligned)
 *   - 104 bytes for ra and the callee-saved GPRs s0-s11
 *   - 96 bytes for the callee-saved FPRs fs0-fs11
 *   - 16 bytes for the output state pointer and the function pointer
 *   - 8 bytes padding
 */

#define STACK_SIZE 224
#define STACK_BASE_GPRS 0
#define STACK_BASE_FPRS 104
#define STACK_OUTPUT 200
#define STACK_FN 208

#define FPR_OFFSET 256

/* Save ra and s0-s11, with CFI offsets relative to CFA = sp + STACK_SIZE. */
.macro save_gprs
        sd ra, (STACK_BASE_GPRS + 0)(sp)
        .cfi_offset ra, -(STACK_SIZE - STACK_BASE_GPRS)
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
        sd s\i, (STACK_BASE_GPRS + 8 + 8*\i)(sp)
        .cfi_offset s\i, -(STACK_SIZE - STACK_BASE_GPRS - 8 - 8*\i)
        .endr
.endm

.macro restore_gprs
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
        ld s\i, (STACK_BASE_GPRS + 8 + 8*\i)(sp)
        .cfi_restore s\i
        .endr
        ld ra, (STACK_BASE_GPRS + 0)(sp)
        .cfi_restore ra
.endm

#if defined(__riscv_float_abi_double)
.macro save_fprs
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
        fsd fs\i, (STACK_BASE_FPRS + 8*\i)(sp)
        .endr
.endm

.macro restore_fprs
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
        fld fs\i, (STACK_BASE_FPRS + 8*\i)(sp)
        .endr
.endm

/* Seed f0-f31 from the input state pointed to by \base. */
.macro load_fprs base
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, \
                16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31
        fld f\i, (FPR_OFFSET + 8*\i)(\base)
        .endr
.endm

/* Capture f0-f31 in the output state pointed to by \base. */
.macro store_fprs base
        .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, \
                16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31
        fsd f\i, (FPR_OFFSET + 8*\i)(\base)
        .endr
.endm
#else /* __riscv_float_abi_double */
.macro save_fprs
.endm
.macro restore_fprs
.endm
.macro load_fprs base
.endm
.macro store_fprs base
.endm
#endif /* !__riscv_float_abi_double */

.text
.balign 4
.global asm_call_stub_riscv64
asm_call_stub_riscv64:
        .cfi_startproc
        addi sp, sp, -STACK_SIZE
        .cfi_def_cfa_offset STACK_SIZE

        save_gprs
        save_fprs
        sd a1, STACK_OUTPUT(sp)
        sd a2, STACK_FN(sp)

        /* gp and tp are not seeded: record their live values as baseline. */
        sd gp, (8*3)(a0)
        sd tp, (8*4)(a0)

        load_fprs a0

        /* Seed x5-x31 from the input state, loading a0 (x10) last since it
         * holds the input pointer. ra holds the function pointer. */
        ld ra, STACK_FN(sp)
        .irp i, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, \
                21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31
        ld x\i, (8*\i)(a0)
        .endr
        ld a0, (8*10)(a0)

        jalr ra, 0(ra)

        /* Capture gp, tp and x5-x31 in the output state, using ra as the
         * base register. */
        ld ra, STACK_OUTPUT(sp)
        .irp i, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, \
                19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31
        sd x\i, (8*\i)(ra)
        .endr

        store_fprs ra

        restore_fprs
        restore_gprs
        addi sp, sp, STACK_SIZE
        .cfi_def_cfa_offset 0
        ret
        .cfi_endproc

#endif /* MLK_SYS_RISCV64 */
