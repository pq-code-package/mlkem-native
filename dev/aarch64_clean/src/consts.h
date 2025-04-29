/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_DEV_AARCH64_CLEAN_SRC_CONSTS_H
#define MLK_DEV_AARCH64_CLEAN_SRC_CONSTS_H

#include <stdint.h>
#include "../../../common.h"

#define mlk_zetas_mulcache_native MLK_NAMESPACE(zetas_mulcache_native)
extern const int16_t mlk_zetas_mulcache_native[256];

#define mlk_zetas_mulcache_twisted_native \
  MLK_NAMESPACE(zetas_mulcache_twisted_native)
extern const int16_t mlk_zetas_mulcache_twisted_native[256];

#endif /* !MLK_DEV_AARCH64_CLEAN_SRC_CONSTS_H */
