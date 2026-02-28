/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_DEV_FIPS202_X86_64_AUTO_H
#define MLK_DEV_FIPS202_X86_64_AUTO_H
/* Default FIPS202 assembly profile for x86_64 systems */

/*
 * Keccak-f1600
 *
 * We use a scalar x86_64 implementation for single-state
 * Keccak-f1600 that is always available.
 */
#include "keccak_f1600_x1_scalar.h"

/*
 * Keccak-f1600x4
 *
 * If AVX2 is available, we use a vectorized x4 implementation.
 * Otherwise, the frontend falls back to calling Keccak-f1600 four times.
 */
#if defined(MLK_SYS_X86_64_AVX2)
#include "keccak_f1600_x4_avx2.h"
#endif

#endif /* !MLK_DEV_FIPS202_X86_64_AUTO_H */
