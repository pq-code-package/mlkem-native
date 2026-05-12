/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_BACKENDS_H
#define MLK_BACKENDS_H

#include "common.h"

#if defined(MLK_CONFIG_USE_NATIVE_BACKEND_ARITH)
#include MLK_CONFIG_ARITH_BACKEND_FILE
/* Include to enforce consistency of API and implementation,
 * and conduct sanity checks on the backend.
 *
 * Keep this _after_ the inclusion of the backend; otherwise,
 * the sanity checks won't have an effect. */
#if defined(MLK_CHECK_APIS) && !defined(__ASSEMBLER__)
#include "native/api.h"
#endif
#endif /* MLK_CONFIG_USE_NATIVE_BACKEND_ARITH */

#if defined(MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202)
#include MLK_CONFIG_FIPS202_BACKEND_FILE
/* Include to enforce consistency of API and implementation,
 * and conduct sanity checks on the backend.
 *
 * Keep this _after_ the inclusion of the backend; otherwise,
 * the sanity checks won't have an effect. */
#if defined(MLK_CHECK_APIS) && !defined(__ASSEMBLER__)
#include "fips202/native/api.h"
#endif
#endif /* MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 */

#endif /* !MLK_BACKENDS_H */
