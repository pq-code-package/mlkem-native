/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_TEST_ABICHECK_SELFTEST_H
#define MLK_TEST_ABICHECK_SELFTEST_H

/* Run the ABI checker meta-test for the active architecture. Returns the
 * number of selftest failures (0 = all good). */
int abicheck_selftest(void);

#endif /* !MLK_TEST_ABICHECK_SELFTEST_H */
