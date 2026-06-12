/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#ifndef MLK_TEST_ABICHECK_CHECKS_PPC64LE_ALL_H
#define MLK_TEST_ABICHECK_CHECKS_PPC64LE_ALL_H

#include <stddef.h>
#include "../abicheck_common.h"

#if defined(MLK_SYS_PPC64LE)

int check_intt_ppc_asm(void);
int check_ntt_ppc_asm(void);
int check_poly_tomont_ppc_asm(void);
int check_reduce_ppc_asm(void);

static const abicheck_entry_t all_checks[] = {
    {"intt_ppc_asm", check_intt_ppc_asm},
    {"ntt_ppc_asm", check_ntt_ppc_asm},
    {"poly_tomont_ppc_asm", check_poly_tomont_ppc_asm},
    {"reduce_ppc_asm", check_reduce_ppc_asm},
    {NULL, NULL} /* Sentinel */
};

#endif /* MLK_SYS_PPC64LE */

#endif /* !MLK_TEST_ABICHECK_CHECKS_PPC64LE_ALL_H */
