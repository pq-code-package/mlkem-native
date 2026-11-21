/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_AUTO_H
#define MLK_FIPS202_NATIVE_AUTO_H

/*
 * Default FIPS202 backend
 */
#include "../../sys.h"

#if defined(MLK_SYS_AARCH64)
#include "aarch64/auto.h"
#endif

/* The x86_64 backends require toolchain support for the SysV ABI. With
 * AVX-512 (F, VL and DQ), the AVX-512 backend provides both the x1 and the
 * x4 permutation; otherwise, with AVX2, the AVX2 backend provides the x4
 * permutation. */
#if defined(MLK_SYS_X86_64_AVX512) && defined(MLK_SYSV_ABI_SUPPORTED)
#include "x86_64/avx512.h"
#elif defined(MLK_SYS_X86_64_AVX2) && defined(MLK_SYSV_ABI_SUPPORTED)
#include "x86_64/keccak_f1600_x4_avx2.h"
#endif

/* We do not yet include the FIPS202 backend for Armv8.1-M+MVE by default
 * as it is still experimental and undergoing review. */
/* #if defined(MLK_SYS_ARMV81M_MVE) */
/* #include "armv81m/mve.h" */
/* #endif */

#endif /* !MLK_FIPS202_NATIVE_AUTO_H */
