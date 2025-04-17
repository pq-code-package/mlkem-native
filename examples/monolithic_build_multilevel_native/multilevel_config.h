/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_CONFIG_H
#define MLK_CONFIG_H

/******************************************************************************
 * Name:        MLK_CONFIG_PARAMETER_SET
 *
 * Description: Specifies the parameter set for ML-KEM
 *              - MLK_CONFIG_PARAMETER_SET=512 corresponds to ML-KEM-512
 *              - MLK_CONFIG_PARAMETER_SET=768 corresponds to ML-KEM-768
 *              - MLK_CONFIG_PARAMETER_SET=1024 corresponds to ML-KEM-1024
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#ifndef MLK_CONFIG_PARAMETER_SET
#define MLK_CONFIG_PARAMETER_SET \
  768 /* Change this for different security strengths */
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_FILE
 *
 * Description: If defined, this is a header that will be included instead
 *              of mlkem/config.h.
 *
 *              This _must_ be set on the command line using
 *              `-DMLK_CONFIG_FILE="..."`.
 *
 *              When you need to build mlkem-native in multiple configurations,
 *              using varying MLK_CONFIG_FILE can be more convenient
 *              then configuring everything through CFLAGS.
 *
 *****************************************************************************/
/* #define MLK_CONFIG_FILE "config.h" */

/******************************************************************************
 * Name:        MLK_CONFIG_NAMESPACE_PREFIX
 *
 * Description: The prefix to use to namespace global symbols
 *              from mlkem/.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#define MLK_CONFIG_NAMESPACE_PREFIX mlkem

/******************************************************************************
 * Name:        MLK_CONFIG_USE_NATIVE_BACKEND_ARITH
 *
 * Description: Determines whether an native arithmetic backend should be used.
 *
 *              The arithmetic backend covers performance critical functions
 *              such as the number-theoretic transform (NTT).
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the arithmetic backend to be use is
 *              determined by MLK_ARITH_BACKEND: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#define MLK_CONFIG_USE_NATIVE_BACKEND_ARITH

/******************************************************************************
 * Name:        MLK_CONFIG_ARITH_BACKEND_FILE
 *
 * Description: The arithmetic backend to use.
 *
 *              If MLK_CONFIG_USE_NATIVE_BACKEND_ARITH is unset, this option
 *              is ignored.
 *
 *              If MLK_CONFIG_USE_NATIVE_BACKEND_ARITH is set, this option must
 *              either be undefined or the filename of an arithmetic backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLK_CONFIG_USE_NATIVE_BACKEND_ARITH) && \
    !defined(MLK_CONFIG_ARITH_BACKEND_FILE)
#define MLK_CONFIG_ARITH_BACKEND_FILE "native/meta.h"
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
 *
 * Description: Determines whether an native FIPS202 backend should be used.
 *
 *              The FIPS202 backend covers 1x/2x/4x-fold Keccak-f1600, which is
 *              the performance bottleneck of SHA3 and SHAKE.
 *
 *              If this option is unset, the C backend will be used.
 *
 *              If this option is set, the FIPS202 backend to be use is
 *              determined by MLK_FIPS202_BACKEND: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
#define MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202

/******************************************************************************
 * Name:        MLK_CONFIG_FIPS202_BACKEND_FILE
 *
 * Description: The FIPS-202 backend to use.
 *
 *              If MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 is set, this option
 *              must either be undefined or the filename of a FIPS202 backend.
 *              If unset, the default backend will be used.
 *
 *              This can be set using CFLAGS.
 *
 *****************************************************************************/
#if defined(MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202) && \
    !defined(MLK_CONFIG_FIPS202_BACKEND_FILE)
#define MLK_CONFIG_FIPS202_BACKEND_FILE "fips202/native/auto.h"
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_CUSTOM_RANDOMBYTES
 *
 * Description: mlkem-native does not provide a secure randombytes
 *              implementation. Such an implementation has to provided by the
 *              consumer.
 *
 *              If this option is not set, mlkem-native expects a function
 *              void randombytes(uint8_t *out, size_t outlen).
 *
 *              Set this option and define `mlk_randombytes` if you want to
 *              use a custom method to sample randombytes with a different name
 *              or signature.
 *
 *****************************************************************************/

/* Even though we use the default randombytes signature here, registering it
 * as a custom implementation avoids double-declaration of randombytes via
 * mlkem/randombytes.h and test_only_rng/notrandombytes.h: The former is by
 * default included by mlkem-native, and the latter is needed for this example
 * since we rely on the additional randombytes_reset() API. */
#define MLK_CONFIG_CUSTOM_RANDOMBYTES
#if !defined(__ASSEMBLER__)
#include <stdint.h>
#include "sys.h"
#include "test_only_rng/notrandombytes.h"
static MLK_INLINE void mlk_randombytes(uint8_t *ptr, size_t len)
{
  randombytes(ptr, len);
}
#endif

/******************************************************************************
 * Name:        MLK_CONFIG_INTERNAL_API_QUALIFIER
 *
 * Description: If set, this option provides an additional function
 *              qualifier to be added to declarations of internal API.
 *
 *              The primary use case for this option are single-CU builds,
 *              in which case this option can be set to `static`.
 *
 *****************************************************************************/
#define MLK_CONFIG_INTERNAL_API_QUALIFIER static

/******************************************************************************
 * Name:        MLK_CONFIG_EXTERNAL_API_QUALIFIER
 *
 * Description: If set, this option provides an additional function
 *              qualifier to be added to declarations of mlkem-native's
 *              public API.
 *
 *              The primary use case for this option are single-CU builds
 *              where the public API exposed by mlkem-native is wrapped by
 *              another API in the consuming application. In this case,
 *              even mlkem-native's public API can be marked `static`.
 *
 *****************************************************************************/
#define MLK_CONFIG_EXTERNAL_API_QUALIFIER static

#endif /* MLkEM_NATIVE_CONFIG_H */
