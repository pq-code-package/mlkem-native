/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * ABI-checker FIPS202 backend metadata for AArch64.
 *
 * Plugged in via -DMLK_CONFIG_FIPS202_BACKEND_FILE; enables every
 * Keccak asm variant so the ABI checker can link against all of them.
 */

#ifndef MLK_TEST_ABICHECK_FIPS202_AARCH64_H
#define MLK_TEST_ABICHECK_FIPS202_AARCH64_H

#define MLK_FIPS202_AARCH64_NEED_X1_SCALAR
#define MLK_FIPS202_AARCH64_NEED_X1_V84A
#define MLK_FIPS202_AARCH64_NEED_X2_V84A
#define MLK_FIPS202_AARCH64_NEED_X4_V8A_SCALAR_HYBRID
#define MLK_FIPS202_AARCH64_NEED_X4_V8A_V84A_SCALAR_HYBRID

#endif /* !MLK_TEST_ABICHECK_FIPS202_AARCH64_H */
