/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * Implementation from Kyber reference repository
 * https://github.com/pq-crystals/kyber/blob/main/avx2/consts.c
 */

#include "../../../common.h"

#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)

#include "align.h"
#include "consts.h"

#define Q MLKEM_Q
#define MONT -1044     /* 2^16 mod q */
#define QINV -3327     /* q^-1 mod 2^16 */
#define V 20159        /* floor(2^26/q + 0.5) */
#define FHI 1441       /* mont^2/128 */
#define FLO -10079     /* qinv*FHI */
#define MONTSQHI 1353  /* mont^2 */
#define MONTSQLO 20553 /* qinv*MONTSQHI */
#define MASK 4095
#define SHIFT 32

const qdata_t qdata = {{
#define _16XQ 0
    Q,        Q,        Q,        Q,        Q,        Q,
    Q,        Q,        Q,        Q,        Q,        Q,
    Q,        Q,        Q,        Q,

#define _16XQINV 16
    QINV,     QINV,     QINV,     QINV,     QINV,     QINV,
    QINV,     QINV,     QINV,     QINV,     QINV,     QINV,
    QINV,     QINV,     QINV,     QINV,

#define _16XV 32
    V,        V,        V,        V,        V,        V,
    V,        V,        V,        V,        V,        V,
    V,        V,        V,        V,

#define _16XFLO 48
    FLO,      FLO,      FLO,      FLO,      FLO,      FLO,
    FLO,      FLO,      FLO,      FLO,      FLO,      FLO,
    FLO,      FLO,      FLO,      FLO,

#define _16XFHI 64
    FHI,      FHI,      FHI,      FHI,      FHI,      FHI,
    FHI,      FHI,      FHI,      FHI,      FHI,      FHI,
    FHI,      FHI,      FHI,      FHI,

#define _16XMONTSQLO 80
    MONTSQLO, MONTSQLO, MONTSQLO, MONTSQLO, MONTSQLO, MONTSQLO,
    MONTSQLO, MONTSQLO, MONTSQLO, MONTSQLO, MONTSQLO, MONTSQLO,
    MONTSQLO, MONTSQLO, MONTSQLO, MONTSQLO,

#define _16XMONTSQHI 96
    MONTSQHI, MONTSQHI, MONTSQHI, MONTSQHI, MONTSQHI, MONTSQHI,
    MONTSQHI, MONTSQHI, MONTSQHI, MONTSQHI, MONTSQHI, MONTSQHI,
    MONTSQHI, MONTSQHI, MONTSQHI, MONTSQHI,

#define _16XMASK 112
    MASK,     MASK,     MASK,     MASK,     MASK,     MASK,
    MASK,     MASK,     MASK,     MASK,     MASK,     MASK,
    MASK,     MASK,     MASK,     MASK,

#define _REVIDXB 128
    3854,     3340,     2826,     2312,     1798,     1284,
    770,      256,      3854,     3340,     2826,     2312,
    1798,     1284,     770,      256,

#define _REVIDXD 144
    7,        0,        6,        0,        5,        0,
    4,        0,        3,        0,        2,        0,
    1,        0,        0,        0,

#define _ZETAS_EXP 160
#include "x86_64_zetas.i"

#define _16XSHIFT 624
    SHIFT,    SHIFT,    SHIFT,    SHIFT,    SHIFT,    SHIFT,
    SHIFT,    SHIFT,    SHIFT,    SHIFT,    SHIFT,    SHIFT,
    SHIFT,    SHIFT,    SHIFT,    SHIFT}};

#else /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */

/* Dummy declaration for compilers disliking empty compilation units */
#define empty_cu_consts MLKEM_NAMESPACE(empty_cu_consts)
int empty_cu_consts;
#endif /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */
