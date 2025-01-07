/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* Two instances of mlkem-native for two security levels */

#define MLKEM_NATIVE_CONFIG_FILE "config_512.h"
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE

#define MLKEM_NATIVE_CONFIG_FILE "config_768.h"
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE

#define MLKEM_NATIVE_CONFIG_FILE "config_1024.h"
#include "mlkem_native_monobuild.c"
#undef MLKEM_NATIVE_CONFIG_FILE
