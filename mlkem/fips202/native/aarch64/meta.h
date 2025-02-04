/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_META_H
#define MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_META_H
/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef FIPS202_NATIVE_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define FIPS202_NATIVE_PROFILE_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT

#define MLKEM_NATIVE_FIPS202_BACKEND_NAME AARCH64_DEFAULT

/* Filename of the C backend implementation.
 * This is not inlined here because this header is included in assembly
 * files as well. */
#define MLKEM_NATIVE_FIPS202_BACKEND_IMPL "native/aarch64/src/default_impl.h"

#endif /* FIPS202_NATIVE_PROFILE_H */

#endif /* MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_META_H */
