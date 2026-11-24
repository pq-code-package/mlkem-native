/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_X86_64_AUTO_H
#define MLK_FIPS202_NATIVE_X86_64_AUTO_H
/* Default FIPS202 assembly profile for x86_64 systems */

/*
 * Default logic to decide which implementation to use.
 *
 * Each function has a single implementation. If its capability check
 * fails at runtime (see MLK_CONFIG_CUSTOM_CAPABILITY_FUNC), the function
 * falls back to the default C code, not to another x86_64
 * implementation. For example, if AVX-512 is enabled at compile time but
 * the AVX-512 check fails, Keccak-f1600x4 is computed by four calls to
 * Keccak-f1600, which runs in C; the AVX2 implementation of
 * Keccak-f1600x4 is not used.
 */

/*
 * Keccak-f1600
 *
 * - If AVX-512 (F, VL and DQ) is enabled, we use the AVX-512
 *   implementation.
 * - Otherwise, we fall back to the standard C implementation.
 */
#if defined(MLK_SYS_X86_64_AVX512)
#include "keccak_f1600_x1_avx512.h"
#endif

/*
 * Keccak-f1600x4
 *
 * - If AVX-512 (F, VL and DQ) is enabled, we use the AVX-512
 *   implementation.
 * - Otherwise, if AVX2 is enabled, we use the AVX2 implementation.
 * - Otherwise, Keccak-f1600x4 is computed by four calls to Keccak-f1600.
 */
#if defined(MLK_SYS_X86_64_AVX512)
#include "keccak_f1600_x4_avx512.h"
#elif defined(MLK_SYS_X86_64_AVX2)
#include "keccak_f1600_x4_avx2.h"
#endif

#endif /* !MLK_FIPS202_NATIVE_X86_64_AUTO_H */
