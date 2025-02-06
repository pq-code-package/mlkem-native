/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#if !defined(MLK_ALL_H)
#define MLK_ALL_H

/* API for MLKEM-512 */
#define MLK_BUILD_INFO_LVL 512
#define MLK_BUILD_INFO_NAMESPACE(sym) mlkem512_##sym
#define MLK_BUILD_INFO_NO_STANDARD_API
#include "mlkem_native/mlkem/mlkem_native.h"
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
#undef MLK_BUILD_INFO_NO_STANDARD_API
#undef MLK_H

/* API for MLKEM-768 */
#define MLK_BUILD_INFO_LVL 768
#define MLK_BUILD_INFO_NAMESPACE(sym) mlkem768_##sym
#define MLK_BUILD_INFO_NO_STANDARD_API
#include "mlkem_native/mlkem/mlkem_native.h"
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
#undef MLK_BUILD_INFO_NO_STANDARD_API
#undef MLK_H

/* API for MLKEM-1024 */
#define MLK_BUILD_INFO_LVL 1024
#define MLK_BUILD_INFO_NAMESPACE(sym) mlkem1024_##sym
#define MLK_BUILD_INFO_NO_STANDARD_API
#include "mlkem_native/mlkem/mlkem_native.h"
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
#undef MLK_BUILD_INFO_NO_STANDARD_API
#undef MLK_H

#endif /* MLK_ALL_H */
