/*
 * Copyright (c) 2024 The mlkem-native project authors
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
#define MLKEM_K 3 /* We want MLKEM-768 */

/******************************************************************************
 * Name:        MLKEM_NATIVE_CONFIG_FILE
 *
 * Description: If defined, this is a header that will be included instead
 *              of mlkem/config.h.
 *
 *              When you need to build mlkem-native in multiple configurations,
 *              this can be a convenient alternative to configuration via
 *              CFLAGS.
 *
 *****************************************************************************/
/* No need to set this -- we _are_ already in a custom config */
/* #define MLKEM_NATIVE_CONFIG_FILE "config.h" */

/******************************************************************************
 * Name:        MLKEM_NAMESPACE
 *              _MLKEM_NAMESPACE
 *
 * Description: The macros to use to namespace global symbols
 *              from mlkem/.
 *****************************************************************************/
#define __CONC(a, b) a##b
#define CONC(a, b) __CONC(a, b)

#define MLKEM_NAMESPACE(sym) CONC(CUSTOM_TINY_SHA3_, sym)

/******************************************************************************
 * Name:        FIPS202_NAMESPACE
 *              _FIPS202_NAMESPACE
 *
 * Description: The macros to use to namespace global symbols
 *              from mlkem/fips202/.
 *****************************************************************************/
#define FIPS202_NAMESPACE(sym) CONC(CUSTOM_TINY_SHA3_, sym)

/******************************************************************************
 * Name:        MLKEM_USE_NATIVE
 *
 * Description: Determines whether a native backend should
 *              be used, if available.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#define MLKEM_USE_NATIVE

/******************************************************************************
 * Name:        MLKEM_NATIVE_ARITH_BACKEND
 *
 * Description: The arithmetic backend to use.
 *
 *              This must be the filename of an arithmetic
 *              backend. The backend is expected to define
 *
 *              - MLKEM_NATIVE_ARITH_BACKEND_NAME
 *
 *                The name of the backend as used in the default namespace.
 *
 *              - MLKEM_NATIVE_ARITH_BACKEND_IMPL
 *
 *                The filename of the implementation of the arithmetic backend.
 *
 *              See the existing backends for more information.
 *
 *****************************************************************************/
/* Let's pretend we don't want an arithmetic backend */
/* #define MLKEM_NATIVE_ARITH_BACKEND "native/default.h" */

/******************************************************************************
 * Name:        MLKEM_NATIVE_FIPS202_BACKEND
 *
 * Description: The FIPS-202 backend to use.
 *
 *              This must be the filename of an FIPS-202
 *              backend. The backend is expected to define
 *
 *              - MLKEM_NATIVE_FIPS202_BACKEND_NAME
 *
 *                The name of the backend as used in the default namespace.
 *
 *              - MLKEM_NATIVE_FIPS202_BACKEND_IMPL
 *
 *                The filename of the implementation of the FIPS-202 backend.
 *
 *              See the existing backends for more information.
 *
 *****************************************************************************/
#define MLKEM_NATIVE_FIPS202_BACKEND "fips202/native/custom/custom.h"

/******************************************************************************
 * Name:        MLKEM_NATIVE_API_STANDARD
 *
 * Description: Define this to extend api.h to also export key sizes and public
 *              API in the CRYPTO_xxx and crypto_kem_xxx format as used e.g. by
 *              SUPERCOP.
 *
 *****************************************************************************/
#define MLKEM_NATIVE_API_STANDARD

#endif /* MLkEM_NATIVE_CONFIG_H */
