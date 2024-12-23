/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          Do not modify it directly.
 */

#include "../../../common.h"

#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)
#include "arith_native_x86_64.h"

/*
 * Table of zeta values used in the AVX2 mulcache_compute
 * See autogenerate_files.py for details.
 */

ALIGN const int16_t zetas_mulcache_avx2[128] = {
    -1103, 555,   -1251, 1550,  422,  177,  -291,  1574,  -246,  1159,  -777,
    -602,  -1590, -872,  418,   -156, 430,  843,   871,   105,   587,   -235,
    -460,  1653,  778,   -147,  1483, 1119, 644,   349,   329,   -75,   817,
    603,   1322,  -1465, -1215, 1218, -874, -1187, -1185, -1278, -1510, -870,
    -108,  996,   958,   1522,  1097, 610,  -1285, 384,   -136,  -1335, 220,
    -1659, -1530, 794,   -854,  478,  -308, 991,   -1460, 1628,
};

#else /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */

#define empty_cu_zetas_mulcache_avx2 \
  MLKEM_NAMESPACE_K(empty_cu_zetas_mulcache_avx2)
int empty_cu_zetas_mulcache_avx2;

#endif /* MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT */
