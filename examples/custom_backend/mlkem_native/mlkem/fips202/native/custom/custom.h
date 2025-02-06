/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef MLK_FIPS202_NATIVE_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLK_FIPS202_NATIVE_PROFILE_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLK_FIPS202_BACKEND_CUSTOM_TINY_SHA3

#define MLK_FIPS202_BACKEND_NAME TINY_SHA3

/* Filename of the C backend implementation.
 * This is not inlined here because this header is included in assembly
 * files as well. */
#define MLK_FIPS202_BACKEND_IMPL "fips202/native/custom/src/custom_impl.h"

#endif /* MLK_FIPS202_NATIVE_PROFILE_H */
