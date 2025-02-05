/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLKEM_NATIVE_FIPS202_NATIVE_META_H
#define MLKEM_NATIVE_FIPS202_NATIVE_META_H

/*
 * Default FIPS202 backend
 */
#include "../../sys.h"

#if defined(SYS_AARCH64)
#include "aarch64/meta.h"
#endif

#if defined(SYS_X86_64) && defined(SYS_X86_64_AVX2)
#include "x86_64/meta.h"
#endif

#endif /* MLKEM_NATIVE_FIPS202_NATIVE_META_H */
