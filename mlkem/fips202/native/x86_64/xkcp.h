/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLKEM_NATIVE_FIPS202_NATIVE_X86_64_XKCP_H
#define MLKEM_NATIVE_FIPS202_NATIVE_X86_64_XKCP_H
/* Default FIPS202 assembly profile for AArch64 systems */

#ifdef MLKEM_NATIVE_FIPS202_PROFILE_H
#error Only one FIPS202 assembly profile can be defined -- did you include multiple profiles?
#else
#define MLKEM_NATIVE_FIPS202_PROFILE_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP

#define MLKEM_NATIVE_FIPS202_BACKEND_NAME X86_64_XKCP

/* Filename of the C backend implementation.
 * This is not inlined here because this header is included in assembly
 * files as well. */
#define MLKEM_NATIVE_FIPS202_BACKEND_IMPL \
  "../fips202/native/x86_64/src/xkcp_impl.h"

#endif /* MLKEM_NATIVE_FIPS202_PROFILE_H */

#endif /* MLKEM_NATIVE_FIPS202_NATIVE_X86_64_XKCP_H */
