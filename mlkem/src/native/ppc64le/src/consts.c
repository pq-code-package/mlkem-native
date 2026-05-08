/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
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
    ,
/* twisted zetas for NTT (Barrett-style fqmul: z_tw = round(z*2^16/q)/2) */
#include "consts_ntt_tw.inc"
    ,
/* packed (zeta, twisted) zetas for layer 6+7 in the merged 4-5-6-7 pass */
#include "consts_ntt_layer67_packed.inc"
};
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
