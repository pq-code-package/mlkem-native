/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_X86_64_AVX512_H
#define MLK_FIPS202_NATIVE_X86_64_AVX512_H

/*
 * FIPS202 backend for x86_64 with AVX-512 (F, VL and DQ): Keccak-f1600 for
 * one state and for four states at a time.
 *
 * The default FIPS202 backend (fips202/native/auto.h) is this one if
 * AVX-512F, AVX-512VL and AVX-512DQ are enabled at compile time.
 */

#include "keccak_f1600_x1_avx512.h"
#include "keccak_f1600_x4_avx512.h"

#endif /* !MLK_FIPS202_NATIVE_X86_64_AVX512_H */
