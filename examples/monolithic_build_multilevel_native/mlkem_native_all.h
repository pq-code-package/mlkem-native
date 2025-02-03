/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#if !defined(MLKEM_NATIVE_ALL_H)
#define MLKEM_NATIVE_ALL_H

/* API for MLKEM-512 */
#define BUILD_INFO_LVL 512
#define BUILD_INFO_NAMESPACE(sym) mlkem512_##sym
#define BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef BUILD_INFO_LVL
#undef BUILD_INFO_NAMESPACE
#undef BUILD_INFO_NO_STANDARD_API
#undef MLKEM_NATIVE_H

/* API for MLKEM-768 */
#define BUILD_INFO_LVL 768
#define BUILD_INFO_NAMESPACE(sym) mlkem768_##sym
#define BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef BUILD_INFO_LVL
#undef BUILD_INFO_NAMESPACE
#undef BUILD_INFO_NO_STANDARD_API
#undef MLKEM_NATIVE_H

/* API for MLKEM-1024 */
#define BUILD_INFO_LVL 1024
#define BUILD_INFO_NAMESPACE(sym) mlkem1024_##sym
#define BUILD_INFO_NO_STANDARD_API
#include "mlkem_native.h"
#undef BUILD_INFO_LVL
#undef BUILD_INFO_NAMESPACE
#undef BUILD_INFO_NO_STANDARD_API
#undef MLKEM_NATIVE_H

#endif /* MLKEM_NATIVE_ALL_H */
