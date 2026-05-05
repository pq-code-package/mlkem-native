/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_NATIVE_PPC64LE_SRC_CONSTS_H
#define MLK_NATIVE_PPC64LE_SRC_CONSTS_H
#include "../../../common.h"

/* Offsets into the constant table */
/* check-magic: off */
#define MLK_PPC_NQ_OFFSET 0
#define MLK_PPC_QINV_OFFSET 16
#define MLK_PPC_Q_OFFSET 32
#define MLK_PPC_C20159_OFFSET 48
#define MLK_PPC_C1441_OFFSET 64
#define MLK_PPC_C1353_OFFSET 80
#define MLK_PPC_ZETA_NTT_OFFSET 96
#define MLK_PPC_ZETA_INTT_OFFSET 1104
/* check-magic: on */

#ifndef __ASSEMBLER__
#define mlk_ppc_qdata MLK_NAMESPACE(ppc_qdata)
extern const int16_t mlk_ppc_qdata[];
#endif

#endif /* !MLK_NATIVE_PPC64LE_SRC_CONSTS_H */
