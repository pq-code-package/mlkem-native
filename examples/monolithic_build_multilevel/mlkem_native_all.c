/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Three instances of mlkem-native for all security levels */

#define MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS

#define MLKEM_NATIVE_CONFIG_FILE "config_512.h"
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE

#define MLKEM_NATIVE_MONOBUILD_NO_FIPS202_SOURCES

#define MLKEM_NATIVE_CONFIG_FILE "config_768.h"
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE

#define MLKEM_NATIVE_CONFIG_FILE "config_1024.h"
#undef MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE
