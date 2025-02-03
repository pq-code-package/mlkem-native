/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifdef MLKEM_NATIVE_ARITH_PROFILE_H
#error Only one MLKEM_ARITH assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_NATIVE_ARITH_PROFILE_H

#define MLKEM_NATIVE_ARITH_BACKEND_NAME DUMMY_BACKEND

/* Filename of the C backend implementation.
 * This is not inlined here because this header is included in assembly
 * files as well. */
#define MLKEM_NATIVE_ARITH_BACKEND_IMPL "dummy_backend_impl.h"

#endif /* MLKEM_NATIVE_ARITH_PROFILE_H */
