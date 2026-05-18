/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * ABI-checker FIPS202 backend metadata for x86_64.
 *
 * Plugged in via -DMLK_CONFIG_FIPS202_BACKEND_FILE; enables the AVX2
 * Keccak variant so the ABI checker can link against it.
 */

#ifndef MLK_TEST_ABICHECK_FIPS202_X86_64_H
#define MLK_TEST_ABICHECK_FIPS202_X86_64_H

#define MLK_FIPS202_X86_64_NEED_X4_AVX2

#endif /* !MLK_TEST_ABICHECK_FIPS202_X86_64_H */
