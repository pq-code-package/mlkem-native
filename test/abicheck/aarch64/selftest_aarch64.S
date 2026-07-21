/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../mlkem/src/sys.h"

/*
 * AArch64 selftest stubs.
 *
 * Each function clobbers exactly one callee-saved register and returns:
 * `mvn x,x` for GPRs and `fneg d,d` for D-regs. Both unconditionally flip
 * a bit (mvn inverts all bits; fneg inverts bit 63 even for zero/NaN), so
 * the integer-compare in check_aarch64_aapcs_compliance always fires. The
 * noop produces zero violations.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4

/* Emit a global label (Apple wants a leading underscore) and a one-line
 * body. Mirrors the .macro use in callstub_aarch64.S and the corrupter
 * macros in selftest_ppc64le.S / selftest_armv81m.S. */
.macro define_corrupter name, body
#ifdef __APPLE__
.global _\name
_\name:
#else
.global \name
\name:
#endif
        \body
        ret
.endm

define_corrupter selftest_aarch64_noop

/* x18 is the platform register on Darwin (reserved by the OS, must not be
 * touched) and unused on ELF/Linux. We still expect every kernel-under-test
 * to leave it alone, so the compliance check verifies preservation; this
 * selftest ensures the checker actually fires when x18 is clobbered.
 * Skipped on Apple (the consumer in selftest.c also guards out the extern
 * decl and the registry slot under !__APPLE__) since we can't safely mvn it. */
#if !defined(__APPLE__)
define_corrupter selftest_aarch64_corrupt_x18, "mvn x18, x18"
#endif

/* GPRs: callee-saved set is x19-x29. */
define_corrupter selftest_aarch64_corrupt_x19, "mvn x19, x19"
define_corrupter selftest_aarch64_corrupt_x20, "mvn x20, x20"
define_corrupter selftest_aarch64_corrupt_x21, "mvn x21, x21"
define_corrupter selftest_aarch64_corrupt_x22, "mvn x22, x22"
define_corrupter selftest_aarch64_corrupt_x23, "mvn x23, x23"
define_corrupter selftest_aarch64_corrupt_x24, "mvn x24, x24"
define_corrupter selftest_aarch64_corrupt_x25, "mvn x25, x25"
define_corrupter selftest_aarch64_corrupt_x26, "mvn x26, x26"
define_corrupter selftest_aarch64_corrupt_x27, "mvn x27, x27"
define_corrupter selftest_aarch64_corrupt_x28, "mvn x28, x28"
define_corrupter selftest_aarch64_corrupt_x29, "mvn x29, x29"

/* AAPCS64 preserves only the low 64 bits of v8-v15; fneg d touches just the
 * sign bit of that range. */
#if defined(MLK_SYS_AARCH64_NEON)
define_corrupter selftest_aarch64_corrupt_d8,  "fneg d8,  d8"
define_corrupter selftest_aarch64_corrupt_d9,  "fneg d9,  d9"
define_corrupter selftest_aarch64_corrupt_d10, "fneg d10, d10"
define_corrupter selftest_aarch64_corrupt_d11, "fneg d11, d11"
define_corrupter selftest_aarch64_corrupt_d12, "fneg d12, d12"
define_corrupter selftest_aarch64_corrupt_d13, "fneg d13, d13"
define_corrupter selftest_aarch64_corrupt_d14, "fneg d14, d14"
define_corrupter selftest_aarch64_corrupt_d15, "fneg d15, d15"
#endif /* MLK_SYS_AARCH64_NEON */
