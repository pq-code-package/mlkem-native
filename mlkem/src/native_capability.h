/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_CAPABILITY_H
#define MLK_NATIVE_CAPABILITY_H

#include <stddef.h>
#include <stdint.h>

#include "cbmc.h"
#include "common.h"

#define MLK_NATIVE_FUNC_SUCCESS (0)
#define MLK_NATIVE_FUNC_FAIL (-1)

#if !defined(MLK_CONFIG_CUSTOM_NATIVE_CAPABILITY_FUNC)
static MLK_INLINE int mlk_is_native_capable(void)
__contract__(
  ensures(return_value == 0 || return_value == 1)
) { return 1; }
#endif /* !MLK_CONFIG_CUSTOM_NATIVE_CAPABILITY_FUNC */

#endif /* !MLK_NATIVE_CAPABILITY_H */
