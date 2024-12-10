/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef PARAMS_H
#define PARAMS_H

#include "common.h"
#include "config.h"
#include "cpucap.h"

#ifndef MLKEM_K
#define MLKEM_K 3 /* Change this for different security strengths */
#endif

#if defined(MLKEM_USE_NATIVE_X86_64)
#define MLKEM_NATIVE_BACKEND X86_64
#elif defined(MLKEM_USE_NATIVE_AARCH64)
#define MLKEM_NATIVE_BACKEND AARCH64
#else
#define MLKEM_NATIVE_BACKEND C
#endif

/* Don't change parameters below this line */
#if (MLKEM_K == 2)
#define MLKEM_PARAM_NAME MLKEM512
#elif (MLKEM_K == 3)
#define MLKEM_PARAM_NAME MLKEM768
#elif (MLKEM_K == 4)
#define MLKEM_PARAM_NAME MLKEM1024
#else
#error "MLKEM_K must be in {2,3,4}"
#endif

#define ___MLKEM_NAMESPACE(x1, x2, x3, x4) x1##_##x2##_##x3##_##x4
#define __MLKEM_NAMESPACE(x1, x2, x3, x4) ___MLKEM_NAMESPACE(x1, x2, x3, x4)

/*
 * NAMESPACE is PQCP_MLKEM_NATIVE_<PARAM_NAME>_<BACKEND>_
 * e.g., PQCP_MLKEM_NATIVE_MLKEM512_AARCH64_
 */
#define MLKEM_NAMESPACE(s)                                                     \
  __MLKEM_NAMESPACE(PQCP_MLKEM_NATIVE, MLKEM_PARAM_NAME, MLKEM_NATIVE_BACKEND, \
                    s)
#define _MLKEM_NAMESPACE(s)                               \
  __MLKEM_NAMESPACE(_PQCP_MLKEM_NATIVE, MLKEM_PARAM_NAME, \
                    MLKEM_NATIVE_BACKEND, s)

#define MLKEM_N 256
#define MLKEM_Q 3329
#define UINT12_MAX 4095

#define MLKEM_SYMBYTES 32 /* size in bytes of hashes, and seeds */
#define MLKEM_SSBYTES 32  /* size in bytes of shared key */

#define MLKEM_POLYBYTES 384
#define MLKEM_POLYVECBYTES (MLKEM_K * MLKEM_POLYBYTES)

#if MLKEM_K == 2
#define MLKEM_ETA1 3
#define MLKEM_POLYCOMPRESSEDBYTES_DV 128
#define MLKEM_POLYCOMPRESSEDBYTES_DU 320
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#elif MLKEM_K == 3
#define MLKEM_ETA1 2
#define MLKEM_POLYCOMPRESSEDBYTES_DV 128
#define MLKEM_POLYCOMPRESSEDBYTES_DU 320
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#elif MLKEM_K == 4
#define MLKEM_ETA1 2
#define MLKEM_POLYCOMPRESSEDBYTES_DV 160
#define MLKEM_POLYCOMPRESSEDBYTES_DU 352
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#endif

#define MLKEM_ETA2 2

#define MLKEM_INDCPA_MSGBYTES (MLKEM_SYMBYTES)
#define MLKEM_INDCPA_PUBLICKEYBYTES (MLKEM_POLYVECBYTES + MLKEM_SYMBYTES)
#define MLKEM_INDCPA_SECRETKEYBYTES (MLKEM_POLYVECBYTES)
#define MLKEM_INDCPA_BYTES \
  (MLKEM_POLYVECCOMPRESSEDBYTES_DU + MLKEM_POLYCOMPRESSEDBYTES_DV)

#define MLKEM_PUBLICKEYBYTES (MLKEM_INDCPA_PUBLICKEYBYTES)
/* 32 bytes of additional space to save H(pk) */
#define MLKEM_SECRETKEYBYTES                                   \
  (MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES + \
   2 * MLKEM_SYMBYTES)
#define MLKEM_CIPHERTEXTBYTES (MLKEM_INDCPA_BYTES)

#define KECCAK_WAY 4
#endif
