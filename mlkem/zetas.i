/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          Do not modify it directly.
 */

#include "common.h"
#if !defined(MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED)
#include "ntt.h"

/*
 * Tables of zeta values used in the reference NTT and inverse NTT.
 * See autogen for details.
 */

/* Constant zeta values for NTT layers 1, 2, and 3 */
#define l1zeta1 MLKEM_NAMESPACE(l1zeta1)
static const int16_t l1zeta1 = -758;
#define l2zeta2 MLKEM_NAMESPACE(l2zeta2)
static const int16_t l2zeta2 = -359;
#define l2zeta3 MLKEM_NAMESPACE(l2zeta3)
static const int16_t l2zeta3 = -1517;
#define l3zeta4 MLKEM_NAMESPACE(l3zeta4)
static const int16_t l3zeta4 = 1493;
#define l3zeta5 MLKEM_NAMESPACE(l3zeta5)
static const int16_t l3zeta5 = 1422;
#define l3zeta6 MLKEM_NAMESPACE(l3zeta6)
static const int16_t l3zeta6 = 287;
#define l3zeta7 MLKEM_NAMESPACE(l3zeta7)
static const int16_t l3zeta7 = 202;

/* Zeta values for layer 4, originally occupying */
/* positions 8 .. 15 in the full Zeta table.     */
#define layer4_zetas MLKEM_NAMESPACE(layer4_zetas)
ALIGN static const int16_t layer4_zetas[8] = {
    -171, 622, 1577, 182, 962, -1202, -1474, 1468,
};

#else /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */

#define empty_cu_zetas MLKEM_NAMESPACE_K(empty_cu_zetas)
int empty_cu_zetas;

#endif /* MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED */

/* Zeta values for layer 5, originally occupying 'even'      */
/* positions 16,18,20,22,24,26,28,30 in the full Zeta table. */
#define layer5_even_zetas MLKEM_NAMESPACE(layer5_even_zetas)
ALIGN static const int16_t layer5_even_zetas[8] = {
    573, 264, -829, -1602, -681, 732, -1542, -205,
};

/* Zeta values for layer 5, originally occupying 'odd'       */
/* positions 17,19,21,23,25,27,29,31 in the full Zeta table. */
#define layer5_odd_zetas MLKEM_NAMESPACE(layer5_odd_zetas)
ALIGN static const int16_t layer5_odd_zetas[8] = {
    -1325, 383, 1458, -130, 1017, 608, 411, -1571,
};

/* Zeta values for layer 6, originally occupying  */
/* positions 32 .. 63 in the full Zeta table.     */
#define layer6_zetas MLKEM_NAMESPACE(layer6_zetas)
ALIGN static const int16_t layer6_zetas[32] = {
    1223, 652,   -552,  1015, -1293, 1491, -282, -1544, 516, -8,    -320,
    -666, -1618, -1162, 126,  1469,  -853, -90,  -271,  830, 107,   -1421,
    -247, -951,  -398,  961,  -1508, -725, 448,  -1065, 677, -1275,
};

/* Zeta values for layer 7, originally occupying  */
/* positions 64 .. 127 in the full Zeta table.     */
#define layer7_zetas MLKEM_NAMESPACE(layer7_zetas)
ALIGN const int16_t layer7_zetas[64] = {
    -1103, 430,  555,   843,   -1251, 871,   1550,  105,   422,   587,  177,
    -235,  -291, -460,  1574,  1653,  -246,  778,   1159,  -147,  -777, 1483,
    -602,  1119, -1590, 644,   -872,  349,   418,   329,   -156,  -75,  817,
    1097,  603,  610,   1322,  -1285, -1465, 384,   -1215, -136,  1218, -1335,
    -874,  220,  -1187, -1659, -1185, -1530, -1278, 794,   -1510, -854, -870,
    478,   -108, -308,  996,   991,   958,   -1460, 1522,  1628,
};
