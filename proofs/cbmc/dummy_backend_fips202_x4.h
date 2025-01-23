/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifdef MLKEM_NATIVE_FIPS202_PROFILE_H
#error Only one MLKEM_FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_NATIVE_FIPS202_PROFILE_H

#define MLKEM_NATIVE_FIPS202_BACKEND_NAME DUMMY_BACKEND_FIPS202_X2

/* Filename of the C backend implementation.
 * This is not inlined here because this header is included in assembly
 * files as well. */
#define MLKEM_NATIVE_FIPS202_BACKEND_IMPL "dummy_backend_fips202_x4_impl.h"

#endif /* MLKEM_NATIVE_FIPS202_PROFILE_H */
