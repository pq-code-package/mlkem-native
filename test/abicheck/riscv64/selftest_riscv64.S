/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * RISC-V 64 LP64D selftest stubs.
 *
 * Each function clobbers one callee-saved register and returns: GPRs via
 * `not`, FPRs via `fneg.d`. The result always differs from the input.
 *
 * There are no corrupters for gp and tp: the C runtime relies on them (tp
 * points to thread-local storage), and the call stub does not restore them.
 */

#include "../../../mlkem/src/sys.h"

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

#if defined(MLK_SYS_RISCV64)

.text

.global selftest_riscv64_noop
selftest_riscv64_noop:
        ret

/* GPR corrupters s0-s11 */
.macro corrupt_gpr reg
.global selftest_riscv64_corrupt_\reg
selftest_riscv64_corrupt_\reg:
        not \reg, \reg
        ret
.endm

corrupt_gpr s0
corrupt_gpr s1
corrupt_gpr s2
corrupt_gpr s3
corrupt_gpr s4
corrupt_gpr s5
corrupt_gpr s6
corrupt_gpr s7
corrupt_gpr s8
corrupt_gpr s9
corrupt_gpr s10
corrupt_gpr s11

#if defined(__riscv_float_abi_double)
/* FPR corrupters fs0-fs11 */
.macro corrupt_fpr reg
.global selftest_riscv64_corrupt_\reg
selftest_riscv64_corrupt_\reg:
        fneg.d \reg, \reg
        ret
.endm

corrupt_fpr fs0
corrupt_fpr fs1
corrupt_fpr fs2
corrupt_fpr fs3
corrupt_fpr fs4
corrupt_fpr fs5
corrupt_fpr fs6
corrupt_fpr fs7
corrupt_fpr fs8
corrupt_fpr fs9
corrupt_fpr fs10
corrupt_fpr fs11
#endif /* __riscv_float_abi_double */

#endif /* MLK_SYS_RISCV64 */
