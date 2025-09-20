/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_PPC64LE) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include "consts.h"

MLK_ALIGN const int16_t mlk_ppc_qdata[] = {
    /* -Q */
    /* check-magic: -3329 == -1 * MLKEM_Q */
    -3329,
    -3329,
    -3329,
    -3329,
    -3329,
    -3329,
    -3329,
    -3329,
    /* QINV */
    /* check-magic: -3327 == pow(MLKEM_Q,-1,2^16) */
    -3327,
    -3327,
    -3327,
    -3327,
    -3327,
    -3327,
    -3327,
    -3327,
    /* Q */
    3329,
    3329,
    3329,
    3329,
    3329,
    3329,
    3329,
    3329,
    /* check-magic: 20159 == round(2^26 / MLKEM_Q) */
    20159,
    20159,
    20159,
    20159,
    20159,
    20159,
    20159,
    20159,
    /* check-magic: 1441 == pow(2,32-7,MLKEM_Q) */
    1441,
    1441,
    1441,
    1441,
    1441,
    1441,
    1441,
    1441,
    /* check-magic: 1353 == pow(2, 32, MLKEM_Q) */
    1353,
    1353,
    1353,
    1353,
    1353,
    1353,
    1353,
    1353,
/* zetas for NTT */
#include "consts_ntt.inc"
    ,
/* zetas for invNTT */
#include "consts_intt.inc"
};

#endif /* MLK_ARITH_BACKEND_PPC64LE && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
