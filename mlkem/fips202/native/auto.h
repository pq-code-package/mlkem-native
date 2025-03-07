/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
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

#if defined(MLK_SYS_X86_64) && defined(MLK_SYS_X86_64_AVX2)
#include "x86_64/xkcp.h"
#endif

#endif /* MLK_FIPS202_NATIVE_AUTO_H */
