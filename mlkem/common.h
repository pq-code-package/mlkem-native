/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLKEM_NATIVE_COMMON_H
#define MLKEM_NATIVE_COMMON_H

#if defined(MLKEM_NATIVE_CONFIG_FILE)
#include MLKEM_NATIVE_CONFIG_FILE
#endif /* MLKEM_NATIVE_CONFIG_FILE */

#include "params.h"
#include "sys.h"
#include "namespace.h"

/* Include backend metadata */
#if defined(MLKEM_USE_NATIVE)
#if defined(MLKEM_NATIVE_ARITH_BACKEND)
#include MLKEM_NATIVE_ARITH_BACKEND
#endif
#if defined(MLKEM_NATIVE_FIPS202_BACKEND)
#include MLKEM_NATIVE_FIPS202_BACKEND
#endif
#endif

#if !defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#define MLKEM_NATIVE_ARITH_BACKEND_NAME C
#endif

#if !defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#define MLKEM_NATIVE_FIPS202_BACKEND_NAME C
#endif

/* On Apple platforms, we need to emit leading underscore
 * in front of assembly symbols. We thus introducee a separate
 * namespace wrapper for ASM symbols. */
#if !defined(__APPLE__)
#define MLKEM_ASM_NAMESPACE(sym) MLKEM_NAMESPACE(sym)
#define FIPS202_ASM_NAMESPACE(sym) FIPS202_NAMESPACE(sym)
#else
#define _PREFIX_UNDERSCORE(sym) _##sym
#define PREFIX_UNDERSCORE(sym) _PREFIX_UNDERSCORE(sym)
#define MLKEM_ASM_NAMESPACE(sym) PREFIX_UNDERSCORE(MLKEM_NAMESPACE(sym))
#define FIPS202_ASM_NAMESPACE(sym) PREFIX_UNDERSCORE(FIPS202_NAMESPACE(sym))
#endif

#endif /* MLKEM_NATIVE_COMMON_H */
