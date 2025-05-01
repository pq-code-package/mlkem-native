/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#if !defined(MLK_ALL_H)
#define MLK_ALL_H

#define MLK_CONFIG_API_NO_SUPERCOP

/* API for MLKEM-512 */
#define MLK_CONFIG_API_PARAMETER_SET 512
#define MLK_CONFIG_API_NAMESPACE_PREFIX mlkem512
#include <mlkem_native.h>
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_H

/* API for MLKEM-768 */
#define MLK_CONFIG_API_PARAMETER_SET 768
#define MLK_CONFIG_API_NAMESPACE_PREFIX mlkem768
#include <mlkem_native.h>
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_H

/* API for MLKEM-1024 */
#define MLK_CONFIG_API_PARAMETER_SET 1024
#define MLK_CONFIG_API_NAMESPACE_PREFIX mlkem1024
#include <mlkem_native.h>
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_CONFIG_API_NO_SUPERCOP
#undef MLK_H

#endif /* !MLK_ALL_H */
