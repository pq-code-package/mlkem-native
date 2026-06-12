/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * AArch64 selftest stubs.
 *
 * Each function clobbers exactly one callee-saved register and returns:
 * `mvn x,x` for GPRs (never identity) and `fneg d,d` for D-regs (differs
 * unless d is exactly zero). The noop produces zero violations.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4

#ifdef __APPLE__
.global _selftest_aarch64_noop
_selftest_aarch64_noop:
#else
.global selftest_aarch64_noop
selftest_aarch64_noop:
#endif
        ret

/* x18 is the platform register on Darwin (reserved by the OS, must not be
 * touched) and unused on ELF/Linux. We still expect every kernel-under-test
 * to leave it alone, so the compliance check verifies preservation; this
 * selftest ensures the checker actually fires when x18 is clobbered.
 * Skipped on Apple (the consumer in selftest.c also guards out the extern
 * decl and the registry slot under !__APPLE__) since we can't safely mvn it. */
#if !defined(__APPLE__)
.global selftest_aarch64_corrupt_x18
selftest_aarch64_corrupt_x18:
        mvn x18, x18
        ret
#endif /* !__APPLE__ */

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x19
_selftest_aarch64_corrupt_x19:
#else
.global selftest_aarch64_corrupt_x19
selftest_aarch64_corrupt_x19:
#endif
        mvn x19, x19
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x20
_selftest_aarch64_corrupt_x20:
#else
.global selftest_aarch64_corrupt_x20
selftest_aarch64_corrupt_x20:
#endif
        mvn x20, x20
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x21
_selftest_aarch64_corrupt_x21:
#else
.global selftest_aarch64_corrupt_x21
selftest_aarch64_corrupt_x21:
#endif
        mvn x21, x21
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x22
_selftest_aarch64_corrupt_x22:
#else
.global selftest_aarch64_corrupt_x22
selftest_aarch64_corrupt_x22:
#endif
        mvn x22, x22
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x23
_selftest_aarch64_corrupt_x23:
#else
.global selftest_aarch64_corrupt_x23
selftest_aarch64_corrupt_x23:
#endif
        mvn x23, x23
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x24
_selftest_aarch64_corrupt_x24:
#else
.global selftest_aarch64_corrupt_x24
selftest_aarch64_corrupt_x24:
#endif
        mvn x24, x24
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x25
_selftest_aarch64_corrupt_x25:
#else
.global selftest_aarch64_corrupt_x25
selftest_aarch64_corrupt_x25:
#endif
        mvn x25, x25
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x26
_selftest_aarch64_corrupt_x26:
#else
.global selftest_aarch64_corrupt_x26
selftest_aarch64_corrupt_x26:
#endif
        mvn x26, x26
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x27
_selftest_aarch64_corrupt_x27:
#else
.global selftest_aarch64_corrupt_x27
selftest_aarch64_corrupt_x27:
#endif
        mvn x27, x27
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x28
_selftest_aarch64_corrupt_x28:
#else
.global selftest_aarch64_corrupt_x28
selftest_aarch64_corrupt_x28:
#endif
        mvn x28, x28
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_x29
_selftest_aarch64_corrupt_x29:
#else
.global selftest_aarch64_corrupt_x29
selftest_aarch64_corrupt_x29:
#endif
        mvn x29, x29
        ret

/* AAPCS64 preserves only the low 64 bits of v8-v15; fneg d touches just the
 * sign bit of that range. */

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d8
_selftest_aarch64_corrupt_d8:
#else
.global selftest_aarch64_corrupt_d8
selftest_aarch64_corrupt_d8:
#endif
        fneg d8, d8
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d9
_selftest_aarch64_corrupt_d9:
#else
.global selftest_aarch64_corrupt_d9
selftest_aarch64_corrupt_d9:
#endif
        fneg d9, d9
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d10
_selftest_aarch64_corrupt_d10:
#else
.global selftest_aarch64_corrupt_d10
selftest_aarch64_corrupt_d10:
#endif
        fneg d10, d10
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d11
_selftest_aarch64_corrupt_d11:
#else
.global selftest_aarch64_corrupt_d11
selftest_aarch64_corrupt_d11:
#endif
        fneg d11, d11
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d12
_selftest_aarch64_corrupt_d12:
#else
.global selftest_aarch64_corrupt_d12
selftest_aarch64_corrupt_d12:
#endif
        fneg d12, d12
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d13
_selftest_aarch64_corrupt_d13:
#else
.global selftest_aarch64_corrupt_d13
selftest_aarch64_corrupt_d13:
#endif
        fneg d13, d13
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d14
_selftest_aarch64_corrupt_d14:
#else
.global selftest_aarch64_corrupt_d14
selftest_aarch64_corrupt_d14:
#endif
        fneg d14, d14
        ret

#ifdef __APPLE__
.global _selftest_aarch64_corrupt_d15
_selftest_aarch64_corrupt_d15:
#else
.global selftest_aarch64_corrupt_d15
selftest_aarch64_corrupt_d15:
#endif
        fneg d15, d15
        ret
