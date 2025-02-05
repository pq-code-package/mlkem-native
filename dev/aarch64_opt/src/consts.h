/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLKEM_NATIVE_DEV_AARCH64_OPT_SRC_CONSTS_H
#define MLKEM_NATIVE_DEV_AARCH64_OPT_SRC_CONSTS_H

#include <stdint.h>
#include "../../../common.h"

#define zetas_mulcache_native MLKEM_NAMESPACE(zetas_mulcache_native)
extern const int16_t zetas_mulcache_native[256];

#define zetas_mulcache_twisted_native \
  MLKEM_NAMESPACE(zetas_mulcache_twisted_native)
extern const int16_t zetas_mulcache_twisted_native[256];

#endif /* MLKEM_NATIVE_DEV_AARCH64_OPT_SRC_CONSTS_H */
