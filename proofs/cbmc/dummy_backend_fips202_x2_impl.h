/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* ML-KEM arithmetic native profile for clean assembly */

#ifdef MLK_ARITH_PROFILE_IMPL_H
#error Only one MLKEM_ARITH assembly profile can be defined -- did you include multiple profiles?
#else
#define MLK_ARITH_PROFILE_IMPL_H

#define MLK_USE_FIPS202_X2_NATIVE

#include "../mlkem/fips202/native/api.h"

#endif /* MLK_ARITH_PROFILE_IMPL_H */
