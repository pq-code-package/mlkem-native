/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_NATIVE_PPC64LE_SRC_CONSTS_H
#define MLK_NATIVE_PPC64LE_SRC_CONSTS_H
#include "../../../common.h"

/* Offsets into the constant table */
/* check-magic: off */
#define NQ_OFFSET 0
#define QINV_OFFSET 16
#define Q_OFFSET 32
#define C20159_OFFSET 48
#define C1441_OFFSET 64
#define C1353_OFFSET 80
#define ZETA_NTT_OFFSET 96
#define ZETA_NTT_OFFSET64 1104
#define IZETA_NTT_OFFSET127 1616
#define IZETA_NTT_OFFSET63 2128
/* check-magic: on */

#ifndef __ASSEMBLER__
#define mlk_ppc_qdata MLK_NAMESPACE(ppc_qdata)
extern const int16_t mlk_ppc_qdata[];
#endif

#endif /* !MLK_NATIVE_PPC64LE_SRC_CONSTS_H */
