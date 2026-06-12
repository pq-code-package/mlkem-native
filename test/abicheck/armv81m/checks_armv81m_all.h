/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef CHECKS_ARMV81M_ALL_H
#define CHECKS_ARMV81M_ALL_H

#include <stddef.h>
#define MLK_BUILD_INTERNAL
#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "../../../mlkem/mlkem_native_config.h"
#endif
#include "../../../mlkem/src/sys.h"

#include "../abicheckutil.h"

#if defined(MLK_SYS_ARMV81M_MVE)

int check_keccak_f1600_x4_mve_asm(void);

static const abicheck_entry_t all_checks[] = {
#if defined(__ARM_FEATURE_MVE)
    {"keccak_f1600_x4_mve_asm", check_keccak_f1600_x4_mve_asm},
#endif
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_ARMV81M_MVE */

#endif /* !CHECKS_ARMV81M_ALL_H */
