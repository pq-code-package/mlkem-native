/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * ABI-checker arith backend metadata for x86_64.
 *
 * Plugged in via -DMLK_CONFIG_ARITH_BACKEND_FILE; selects every gated
 * x86_64 arith asm/data file without dragging in the dispatch glue
 * (MLK_USE_NATIVE_*) that would require compiling indcpa.c / poly.c.
 */

#ifndef MLK_TEST_ABICHECK_ARITH_X86_64_H
#define MLK_TEST_ABICHECK_ARITH_X86_64_H

#define MLK_ARITH_BACKEND_X86_64_DEFAULT

#endif /* !MLK_TEST_ABICHECK_ARITH_X86_64_H */
