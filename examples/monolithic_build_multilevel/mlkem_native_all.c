/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Only include API to check consistency with mlkem/mlkem_native.h
 * imported into the individual builds below via MLK_CHECK_APIS. */
#include "mlkem_native_all.h"

#define MLK_MULTILEVEL_BUILD

/* Include mlkem_native.h into each level-build to ensure consistency
 * with kem.h and mlkem_native_all.h above. */
#define MLK_CHECK_APIS

/* Three instances of mlkem-native for all security levels */

/* Include level-independent code */
#define MLK_MULTILEVEL_BUILD_WITH_SHARED
#define MLK_MONOBUILD_KEEP_SHARED_HEADERS

#define MLKEM_K 2
#define MLK_CONFIG_FILE "multilevel_config.h"
#include "mlkem_native_monobuild.c"
#undef MLK_CONFIG_FILE

/* Exclude level-independent code */
#undef MLK_MULTILEVEL_BUILD_WITH_SHARED
#define MLK_MULTILEVEL_BUILD_NO_SHARED

#define MLKEM_K 3
#define MLK_CONFIG_FILE "multilevel_config.h"
#include "mlkem_native_monobuild.c"
#undef MLK_CONFIG_FILE

#undef MLK_MONOBUILD_KEEP_SHARED_HEADERS

#define MLKEM_K 4
#define MLK_CONFIG_FILE "multilevel_config.h"
#include "mlkem_native_monobuild.c"
#undef MLK_CONFIG_FILE
