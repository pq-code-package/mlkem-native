/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef FIPS202_NATIVE_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define FIPS202_NATIVE_PROFILE_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLKEM_NATIVE_FIPS202_BACKEND_CUSTOM_TINY_SHA3

#define MLKEM_NATIVE_FIPS202_BACKEND_NAME TINY_SHA3

/* Filename of the C backend implementation.
 * This is not inlined here because this header is included in assembly
 * files as well. */
#define MLKEM_NATIVE_FIPS202_BACKEND_IMPL \
  "fips202/native/custom/src/custom_impl.h"

#endif /* FIPS202_NATIVE_PROFILE_H */
