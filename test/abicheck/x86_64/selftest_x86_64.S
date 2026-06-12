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

#ifdef __APPLE__
.global _selftest_x86_64_noop
_selftest_x86_64_noop:
#else
.global selftest_x86_64_noop
selftest_x86_64_noop:
#endif
        ret

#ifdef __APPLE__
.global _selftest_x86_64_corrupt_rbx
_selftest_x86_64_corrupt_rbx:
#else
.global selftest_x86_64_corrupt_rbx
selftest_x86_64_corrupt_rbx:
#endif
        notq    %rbx
        ret

#ifdef __APPLE__
.global _selftest_x86_64_corrupt_rbp
_selftest_x86_64_corrupt_rbp:
#else
.global selftest_x86_64_corrupt_rbp
selftest_x86_64_corrupt_rbp:
#endif
        notq    %rbp
        ret

#ifdef __APPLE__
.global _selftest_x86_64_corrupt_r12
_selftest_x86_64_corrupt_r12:
#else
.global selftest_x86_64_corrupt_r12
selftest_x86_64_corrupt_r12:
#endif
        notq    %r12
        ret

#ifdef __APPLE__
.global _selftest_x86_64_corrupt_r13
_selftest_x86_64_corrupt_r13:
#else
.global selftest_x86_64_corrupt_r13
selftest_x86_64_corrupt_r13:
#endif
        notq    %r13
        ret

#ifdef __APPLE__
.global _selftest_x86_64_corrupt_r14
_selftest_x86_64_corrupt_r14:
#else
.global selftest_x86_64_corrupt_r14
selftest_x86_64_corrupt_r14:
#endif
        notq    %r14
        ret

#ifdef __APPLE__
.global _selftest_x86_64_corrupt_r15
_selftest_x86_64_corrupt_r15:
#else
.global selftest_x86_64_corrupt_r15
selftest_x86_64_corrupt_r15:
#endif
        notq    %r15
        ret
