/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLKEM_NATIVE_CONFIG_H
#define MLKEM_NATIVE_CONFIG_H

/******************************************************************************
 * Name:        MLKEM_K
 *
 * Description: Determines the security level for ML-KEM
 *              - MLKEM_K=2 corresponds to ML-KEM-512
 *              - MLKEM_K=3 corresponds to ML-KEM-768
 *              - MLKEM_K=4 corresponds to ML-KEM-1024
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#ifndef MLKEM_K
#define MLKEM_K 3 /* Change this for different security strengths */
#endif

/******************************************************************************
 * Name:        MLKEM_NATIVE_CONFIG_FILE
 *
 * Description: If defined, this is a header that will be included instead
 *              of mlkem/config.h.
 *
 *              This _must_ be set on the command line using
 *              `-DMLKEM_NATIVE_CONFIG_FILE="..."`.
 *
 *              When you need to build mlkem-native in multiple configurations,
 *              using varying MLKEM_NATIE_CONFIG_FILE can be more convenient
 *              then configuring everything through CFLAGS.
 *
 *****************************************************************************/
/* #define MLKEM_NATIVE_CONFIG_FILE "config.h" */

/******************************************************************************
 * Name:        MLKEM_NAMESPACE_PREFIX
 *
 * Description: The prefix to use to namespace global symbols
 *              from mlkem/.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#define MLKEM_NAMESPACE_PREFIX mlkem
#define MLKEM_NAMESPACE_PREFIX_ADD_LEVEL

/******************************************************************************
 * Name:        MLKEM_USE_NATIVE_BACKEND_ARITH
 *
 * Description: Determines whether an native arithmetic backend should be used.
 *
 *              The arithmetic backend covers performance critical functions
 *              such as the number-theoretic transform (NTT).
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the arithmetic backend to be use is
 *              determined by MLKEM_NATIVE_ARITH_BACKEND: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLKEM_USE_NATIVE_BACKEND_ARITH)
/* #define MLKEM_USE_NATIVE_BACKEND_ARITH */
#endif

/******************************************************************************
 * Name:        MLKEM_NATIVE_ARITH_BACKEND_FILE
 *
 * Description: The arithmetic backend to use.
 *
 *              If MLKEM_USE_NATIVE_BACKEND_ARITH is unset, this option
 *              is ignored.
 *
 *              If MLKEM_USE_NATIVE_BACKEND_ARITH is set, this option must
 *              either be undefined or the filename of an arithmetic backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLKEM_USE_NATIVE_BACKEND_ARITH) && \
    !defined(MLKEM_NATIVE_ARITH_BACKEND_FILE)
#define MLKEM_NATIVE_ARITH_BACKEND_FILE "native/default.h"
#endif

/******************************************************************************
 * Name:        MLKEM_USE_NATIVE_BACKEND_FIPS202
 *
 * Description: Determines whether an native FIPS202 backend should be used.
 *
 *              The FIPS202 backend covers 1x/2x/4x-fold Keccak-f1600, which is
 *              the performance bottleneck of SHA3 and SHAKE.
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the FIPS202 backend to be use is
 *              determined by MLKEM_NATIVE_FIPS202_BACKEND: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#if !defined(MLKEM_USE_NATIVE_BACKEND_FIPS202)
/* #define MLKEM_USE_NATIVE_BACKEND_FIPS202 */
#endif

#endif /* MLkEM_NATIVE_CONFIG_H */
