/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef MLK_TEST_ABICHECK_CHECKS_ARMV81M_ALL_H
#define MLK_TEST_ABICHECK_CHECKS_ARMV81M_ALL_H

#include <stddef.h>
#include "../abicheck_common.h"

#if defined(MLK_SYS_ARMV81M_MVE)

#if defined(__ARM_FEATURE_MVE)
int check_keccak_f1600_x4_mve_asm(void);
#endif

static const abicheck_entry_t all_checks[] = {
#if defined(__ARM_FEATURE_MVE)
    {"keccak_f1600_x4_mve_asm", check_keccak_f1600_x4_mve_asm},
#endif
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_ARMV81M_MVE */

#endif /* !MLK_TEST_ABICHECK_CHECKS_ARMV81M_ALL_H */
