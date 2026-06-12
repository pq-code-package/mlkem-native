/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * x86_64 (System V) selftest stubs.
 *
 * Each function clobbers exactly one callee-saved register and returns.
 * `not %rN` flips every bit of an integer GPR; the result is guaranteed
 * to differ from the input random value.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text

/* Emit a global label (Apple wants a leading underscore) and a one-line
 * body. Mirrors the corrupter macros in selftest_aarch64.S /
 * selftest_ppc64le.S / selftest_armv81m.S. */
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

define_corrupter selftest_x86_64_noop
define_corrupter selftest_x86_64_corrupt_rbx, "notq %rbx"
define_corrupter selftest_x86_64_corrupt_rbp, "notq %rbp"
define_corrupter selftest_x86_64_corrupt_r12, "notq %r12"
define_corrupter selftest_x86_64_corrupt_r13, "notq %r13"
define_corrupter selftest_x86_64_corrupt_r14, "notq %r14"
define_corrupter selftest_x86_64_corrupt_r15, "notq %r15"
