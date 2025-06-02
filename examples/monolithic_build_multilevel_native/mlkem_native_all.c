/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* Three instances of mlkem-native for all security levels */

#define MLK_CONFIG_FILE "multilevel_config.h"

/* Include level-independent code */
#define MLK_CONFIG_MULTILEVEL_WITH_SHARED 1
/* Keep level-independent headers at the end of monobuild file */
#define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#define MLK_CONFIG_PARAMETER_SET 512
#include "mlkem_native.c"
#undef MLK_CONFIG_MULTILEVEL_WITH_SHARED
#undef MLK_CONFIG_PARAMETER_SET

/* Exclude level-independent code */
#define MLK_CONFIG_MULTILEVEL_NO_SHARED
#define MLK_CONFIG_PARAMETER_SET 768
#include "mlkem_native.c"
/* `#undef` all headers at the and of the monobuild file */
#undef MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#undef MLK_CONFIG_PARAMETER_SET

#define MLK_CONFIG_PARAMETER_SET 1024
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
