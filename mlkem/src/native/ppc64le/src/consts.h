/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_NATIVE_PPC64LE_SRC_CONSTS_H
#define MLK_NATIVE_PPC64LE_SRC_CONSTS_H
#include "../../../common.h"

#define NQ_OFFSET 0
#define QINV_OFFSET 16
#define Q_OFFSET 32
#define C20159_OFFSET 48
#define C1441_OFFSET 64
#define C1353_OFFSET 80
#define ZETA_NTT_OFFSET 96
#define ZETA_INTT_OFFSET 1104

#ifndef __ASSEMBLER__
#define mlk_ppc_qdata MLK_NAMESPACE(ppc_qdata)
extern const int16_t mlk_ppc_qdata[];
#else
#define r0 0
#define r1 1
#define r3 3
#define r4 4
#define r5 5
#define r6 6
#define r7 7
#define r8 8
#define r9 9
#define r10 10
#define r11 11
#define r12 12
#define r14 14
#define r15 15
#define r16 16
#define r17 17
#define r18 18
#define r19 19
#define r20 20
#define r21 21
#define v0 0
#define v1 1
#define v2 2
#define v3 3
#define v4 4
#define v5 5
#define v6 6
#define v7 7
#define v8 8
#define v9 9
#define v10 10
#define v11 11
#define v12 12
#define v13 13
#define v14 14
#define v15 15
#define v16 16
#define v17 17
#define v18 18
#define v19 19
#define v20 20
#define v21 21
#define v22 22
#define v23 23
#define v24 24
#define v25 25
#define v26 26
#define v27 27
#define v28 28
#define v29 29
#define v30 30
#define v31 31
#define vs0 0
#define vs1 1
#define vs2 2
#define vs3 3
#define vs4 4
#define vs5 5
#define vs6 6
#define vs7 7
#define vs8 8
#define vs9 9
#define vs10 10
#define vs11 11
#define vs12 12
#define vs13 13
#endif

#endif /* !MLK_NATIVE_PPC64LE_SRC_CONSTS_H */
