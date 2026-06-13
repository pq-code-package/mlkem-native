/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * PowerPC64 ELF v2 selftest stubs.
 *
 * Each function clobbers one callee-saved register and returns: GPRs via
 * `not`, FPRs via `fneg`, VRs by xor'ing in a non-zero pattern from
 * volatile v0, and CR2 via `crnot`. The result always differs from the
 * input.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.machine power8
.abiversion 2

.macro define_local name
.global \name
\name:
        addis   2, 12, (.TOC. - \name)@ha
        addi    2, 2, (.TOC. - \name)@l
        .localentry \name, . - \name
.endm

/* GPR corrupters r14..r31 */
.macro corrupt_gpr name, reg
define_local \name
        not     \reg, \reg
        blr
.endm

/* FPR corrupters f14..f31 */
.macro corrupt_fpr name, reg
define_local \name
        fneg    \reg, \reg
        blr
.endm

/* VR corrupters v20..v31. v0 is volatile scratch under ELFv2; vspltisw + vxor
 * flips the low bit of each lane. */
.macro corrupt_vr name, reg
define_local \name
        vspltisw 0, 1
        vxor    \reg, \reg, 0
        blr
.endm

define_local selftest_ppc64le_noop
        blr

corrupt_gpr selftest_ppc64le_corrupt_r14, 14
corrupt_gpr selftest_ppc64le_corrupt_r15, 15
corrupt_gpr selftest_ppc64le_corrupt_r16, 16
corrupt_gpr selftest_ppc64le_corrupt_r17, 17
corrupt_gpr selftest_ppc64le_corrupt_r18, 18
corrupt_gpr selftest_ppc64le_corrupt_r19, 19
corrupt_gpr selftest_ppc64le_corrupt_r20, 20
corrupt_gpr selftest_ppc64le_corrupt_r21, 21
corrupt_gpr selftest_ppc64le_corrupt_r22, 22
corrupt_gpr selftest_ppc64le_corrupt_r23, 23
corrupt_gpr selftest_ppc64le_corrupt_r24, 24
corrupt_gpr selftest_ppc64le_corrupt_r25, 25
corrupt_gpr selftest_ppc64le_corrupt_r26, 26
corrupt_gpr selftest_ppc64le_corrupt_r27, 27
corrupt_gpr selftest_ppc64le_corrupt_r28, 28
corrupt_gpr selftest_ppc64le_corrupt_r29, 29
corrupt_gpr selftest_ppc64le_corrupt_r30, 30
corrupt_gpr selftest_ppc64le_corrupt_r31, 31

corrupt_fpr selftest_ppc64le_corrupt_f14, 14
corrupt_fpr selftest_ppc64le_corrupt_f15, 15
corrupt_fpr selftest_ppc64le_corrupt_f16, 16
corrupt_fpr selftest_ppc64le_corrupt_f17, 17
corrupt_fpr selftest_ppc64le_corrupt_f18, 18
corrupt_fpr selftest_ppc64le_corrupt_f19, 19
corrupt_fpr selftest_ppc64le_corrupt_f20, 20
corrupt_fpr selftest_ppc64le_corrupt_f21, 21
corrupt_fpr selftest_ppc64le_corrupt_f22, 22
corrupt_fpr selftest_ppc64le_corrupt_f23, 23
corrupt_fpr selftest_ppc64le_corrupt_f24, 24
corrupt_fpr selftest_ppc64le_corrupt_f25, 25
corrupt_fpr selftest_ppc64le_corrupt_f26, 26
corrupt_fpr selftest_ppc64le_corrupt_f27, 27
corrupt_fpr selftest_ppc64le_corrupt_f28, 28
corrupt_fpr selftest_ppc64le_corrupt_f29, 29
corrupt_fpr selftest_ppc64le_corrupt_f30, 30
corrupt_fpr selftest_ppc64le_corrupt_f31, 31

corrupt_vr selftest_ppc64le_corrupt_v20, 20
corrupt_vr selftest_ppc64le_corrupt_v21, 21
corrupt_vr selftest_ppc64le_corrupt_v22, 22
corrupt_vr selftest_ppc64le_corrupt_v23, 23
corrupt_vr selftest_ppc64le_corrupt_v24, 24
corrupt_vr selftest_ppc64le_corrupt_v25, 25
corrupt_vr selftest_ppc64le_corrupt_v26, 26
corrupt_vr selftest_ppc64le_corrupt_v27, 27
corrupt_vr selftest_ppc64le_corrupt_v28, 28
corrupt_vr selftest_ppc64le_corrupt_v29, 29
corrupt_vr selftest_ppc64le_corrupt_v30, 30
corrupt_vr selftest_ppc64le_corrupt_v31, 31

/* CR corrupter. Bit 8 is CR2[0] (CR field n covers bits 4n..4n+3, CR0 high).
 * `crnot` flips it unconditionally, so the captured CR always differs from
 * the seeded value inside MLK_PPC_CR_NV_MASK. */
define_local selftest_ppc64le_corrupt_cr2
        crnot   8, 8
        blr
