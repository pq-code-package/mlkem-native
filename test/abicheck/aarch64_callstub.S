/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../mlkem/src/sys.h"
#if defined(MLK_SYS_AARCH64)

/*
 * Function: asm_call_stub
 * Description: AArch64 ABI compliance testing stub that captures register state
 *              before and after function calls to verify AAPCS compliance
 *
 * C Signature: void asm_call_stub(struct register_state *input,
 *                                 struct register_state *output,
 *                                 void *function_ptr)
 *
 * Register ABI:
 * ```yaml
 *   x0:
 *     type: buffer
 *     size_bytes: 1280
 *     permissions: read-only
 *     c_parameter: struct register_state *input
 *     description: Input register state to load before function call
 *   x1:
 *     type: buffer
 *     size_bytes: 1280
 *     permissions: write-only
 *     c_parameter: struct register_state *output
 *     description: Output buffer to store register state after function call
 *   x2:
 *     type: function_pointer
 *     c_parameter: void *function_ptr
 *     description: Pointer to function under test
 * ```
 *
 * Stack Usage: 192 bytes total (16-byte aligned)
 *   - 112 bytes for saving callee-saved GPRs (x18-x30: 7 pairs * 16 bytes)
 *   - 64 bytes for saving callee-saved NEON registers (d8-d15: 8 regs * 8 bytes)
 *   - 16 bytes for local variables (output state ptr, function ptr)
 *
 */

/*
 * Stack layout constants
 */
#define STACK_SIZE_GPRS   112     /* Space for x18-x30 (7 pairs * 16 bytes = 112 bytes) */
#define STACK_SIZE_VREGS  64      /* Space for d8-d15 (8 registers * 8 bytes = 64 bytes) */
#define STACK_SIZE_LOCALS 16      /* Space for local variables */

#define STACK_SIZE 192
#define STACK_BASE_GPRS 0
#define STACK_BASE_VREGS  STACK_SIZE_GPRS
#define STACK_BASE_LOCALS (STACK_SIZE_GPRS + STACK_SIZE_VREGS)

.macro save_gprs
    stp xzr, x18, [sp, #(STACK_BASE_GPRS + 16*0)]
    stp x19, x20, [sp, #(STACK_BASE_GPRS + 16*1)]
    stp x21, x22, [sp, #(STACK_BASE_GPRS + 16*2)]
    stp x23, x24, [sp, #(STACK_BASE_GPRS + 16*3)]
    stp x25, x26, [sp, #(STACK_BASE_GPRS + 16*4)]
    stp x27, x28, [sp, #(STACK_BASE_GPRS + 16*5)]
    stp x29, x30, [sp, #(STACK_BASE_GPRS + 16*6)]
.endm

.macro restore_gprs
    ldp xzr, x18, [sp, #(STACK_BASE_GPRS + 16*0)]
    ldp x19, x20, [sp, #(STACK_BASE_GPRS + 16*1)]
    ldp x21, x22, [sp, #(STACK_BASE_GPRS + 16*2)]
    ldp x23, x24, [sp, #(STACK_BASE_GPRS + 16*3)]
    ldp x25, x26, [sp, #(STACK_BASE_GPRS + 16*4)]
    ldp x27, x28, [sp, #(STACK_BASE_GPRS + 16*5)]
    ldp x29, x30, [sp, #(STACK_BASE_GPRS + 16*6)]
.endm

.macro save_vregs
        stp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
        stp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
        stp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        stp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

.macro restore_vregs
        ldp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
        ldp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
        ldp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        ldp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

.macro alloc_stack
    sub sp, sp, #(STACK_SIZE)
.endm

.macro free_stack
    add sp, sp, #(STACK_SIZE)
.endm

.text
.balign 4
#ifdef __APPLE__
.global _asm_call_stub
_asm_call_stub:
#else
.global asm_call_stub
asm_call_stub:
#endif
        alloc_stack
        save_gprs
        save_vregs

        /* Save output state address and target function pointer to stack locals.
         * We need to preserve these across register state loading */
        stp x1, x2, [sp, #(STACK_BASE_LOCALS)]

        // Load NEON registers from input state
        add x30, x0,  #256
        ldp q0,  q1,  [x30, #(16*0)]
        ldp q2,  q3,  [x30, #(16*2)]
        ldp q4,  q5,  [x30, #(16*4)]
        ldp q6,  q7,  [x30, #(16*6)]
        ldp q8,  q9,  [x30, #(16*8)]
        ldp q10, q11, [x30, #(16*10)]
        ldp q12, q13, [x30, #(16*12)]
        ldp q14, q15, [x30, #(16*14)]
        ldp q16, q17, [x30, #(16*16)]
        ldp q18, q19, [x30, #(16*18)]
        ldp q20, q21, [x30, #(16*20)]
        ldp q22, q23, [x30, #(16*22)]
        ldp q24, q25, [x30, #(16*24)]
        ldp q26, q27, [x30, #(16*26)]
        ldp q28, q29, [x30, #(16*28)]
        ldp q30, q31, [x30, #(16*30)]
        // Load GPRs from input state
        sub x30, x30, #256
        ldp x0,  x1,  [x0, #(8*0)]
        ldp x2,  x3,  [x30, #(8*2)]
        ldp x4,  x5,  [x30, #(8*4)]
        ldp x6,  x7,  [x30, #(8*6)]
        ldp x8,  x9,  [x30, #(8*8)]
        ldp x10, x11, [x30, #(8*10)]
        ldp x12, x13, [x30, #(8*12)]
        ldp x14, x15, [x30, #(8*14)]
        ldp x16, x17, [x30, #(8*16)]
        ldp x18, x19, [x30, #(8*18)]
        ldp x20, x21, [x30, #(8*20)]
        ldp x22, x23, [x30, #(8*22)]
        ldp x24, x25, [x30, #(8*24)]
        ldp x26, x27, [x30, #(8*26)]
        ldp x28, x29, [x30, #(8*28)]

        // Reload target function pointer (overwriting x30/LR is fine - blr will set it)
        ldr x30, [sp, #(STACK_BASE_LOCALS + 8)]
        // Call target
        blr x30
        // Load output state address (overwrite x30/LR again)
        ldr x30, [sp, #(STACK_BASE_LOCALS + 0)]

        // Store final GPR state to output state
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
        // Note: x30 (LR) not stored as it's meaningless after function call

        // Store final NEON state to output state
        add x30,  x30,  #256
        stp q0,  q1,  [x30, #(16*0)]
        stp q2,  q3,  [x30, #(16*2)]
        stp q4,  q5,  [x30, #(16*4)]
        stp q6,  q7,  [x30, #(16*6)]
        stp q8,  q9,  [x30, #(16*8)]
        stp q10, q11, [x30, #(16*10)]
        stp q12, q13, [x30, #(16*12)]
        stp q14, q15, [x30, #(16*14)]
        stp q16, q17, [x30, #(16*16)]
        stp q18, q19, [x30, #(16*18)]
        stp q20, q21, [x30, #(16*20)]
        stp q22, q23, [x30, #(16*22)]
        stp q24, q25, [x30, #(16*24)]
        stp q26, q27, [x30, #(16*26)]
        stp q28, q29, [x30, #(16*28)]
        stp q30, q31, [x30, #(16*30)]

        restore_vregs
        restore_gprs
        free_stack
        ret

#endif /* MLK_SYS_AARCH64 */
