/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
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
/* This is set on the command line */
/* #define MLK_CONFIG_PARAMETER_SET 768 */

/******************************************************************************
 * Name:        MLK_CONFIG_FILE
 *
 * Description: If defined, this is a header that will be included instead
 *              of mlkem/src/config.h.
 *
 *              When you need to build mlkem-native in multiple configurations,
 *              this can be a convenient alternative to configuration via
 *              CFLAGS.
 *
 *****************************************************************************/
/* No need to set this -- we _are_ already in a custom config */
/* #define MLK_CONFIG_FILE "config.h" */

/******************************************************************************
 * Name:        MLK_CONFIG_NAMESPACE_PREFIX
 *
 * Description: The prefix to use to namespace global symbols
 *              from mlkem/.
 *****************************************************************************/
#define MLK_CONFIG_NAMESPACE_PREFIX CUSTOM_TINY_SHA3

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
 *              determined by MLK_CONFIG_ARITH_BACKEND_FILE: If the latter is
 *              unset, the default backend for your the target architecture
 *              will be used. If set, it must be the name of a backend metadata
 *              file.
 *
 *              This can also be set using CFLAGS.
 *
 *****************************************************************************/
/* No native arithmetic backend */
/* #define MLK_CONFIG_USE_NATIVE_BACKEND_ARITH */

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
/* #define MLK_CONFIG_ARITH_BACKEND_FILE "native/meta.h" */

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
 *              determined by MLK_CONFIG_FIPS202_BACKEND_FILE: If the latter is
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
#define MLK_CONFIG_FIPS202_BACKEND_FILE "fips202/native/custom/custom.h"

#endif /* !MLK_CONFIG_H */
