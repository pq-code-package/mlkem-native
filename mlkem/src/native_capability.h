/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_CAPABILITY_H
#define MLK_NATIVE_CAPABILITY_H

#include <stddef.h>
#include <stdint.h>

#include "common.h"

#if !defined(MLK_CONFIG_CUSTOM_NATIVE_CAPABILITY_FUNC)
static MLK_INLINE int mlk_is_native_capable(void) { return 1; }
#endif

#endif /* !MLK_NATIVE_CAPABILITY_H */
