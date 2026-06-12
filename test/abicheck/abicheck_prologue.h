/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Shared prologue for abicheck sources. Defines MLK_BUILD_INTERNAL (so
 * MLK_CONFIG_FILE's MLK_CONFIG_CUSTOM_CAPABILITY_FUNC body, gated on it,
 * is visible) and pulls in the resolved config + sys.h. We don't include
 * common.h here: it would drag in backend constant tables that older
 * compilers do not drop, forcing them into the abicheck link.
 *
 * Paths use the project's -Imlkem search path (set in test/mk/components.mk)
 * so this header is includable from any depth under test/abicheck/.
 */

#ifndef MLK_TEST_ABICHECK_PROLOGUE_H
#define MLK_TEST_ABICHECK_PROLOGUE_H

#define MLK_BUILD_INTERNAL
#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "mlkem_native_config.h"
#endif
#include "src/sys.h"

#endif /* !MLK_TEST_ABICHECK_PROLOGUE_H */
