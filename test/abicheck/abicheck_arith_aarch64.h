/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * ABI-checker arith backend metadata for AArch64.
 *
 * Plugged in via -DMLK_CONFIG_ARITH_BACKEND_FILE; selects every gated
 * AArch64 arith asm/data file without dragging in the dispatch glue
 * (MLK_USE_NATIVE_*) that would require compiling indcpa.c / poly.c.
 */

#ifndef MLK_TEST_ABICHECK_ARITH_AARCH64_H
#define MLK_TEST_ABICHECK_ARITH_AARCH64_H

#define MLK_ARITH_BACKEND_AARCH64

#endif /* !MLK_TEST_ABICHECK_ARITH_AARCH64_H */
