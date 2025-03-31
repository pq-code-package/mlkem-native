/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_PARAMS_H
#define MLK_PARAMS_H

#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "config.h"
#endif

#if !defined(MLKEM_K)
#error MLKEM_K is not defined
#endif

#define MLKEM_N 256
#define MLKEM_Q 3329
#define MLKEM_Q_HALF ((MLKEM_Q + 1) / 2) /* 1665 */
#define MLKEM_UINT12_LIMIT 4096

#define MLKEM_SYMBYTES 32 /* size in bytes of hashes, and seeds */
#define MLKEM_SSBYTES 32  /* size in bytes of shared key */

#define MLKEM_POLYBYTES 384
#define MLKEM_POLYVECBYTES (MLKEM_K * MLKEM_POLYBYTES)

#define MLKEM_POLYCOMPRESSEDBYTES_D4 128
#define MLKEM_POLYCOMPRESSEDBYTES_D5 160
#define MLKEM_POLYCOMPRESSEDBYTES_D10 320
#define MLKEM_POLYCOMPRESSEDBYTES_D11 352

#if MLKEM_K == 2
#define MLKEM_LVL 512
#define MLKEM_ETA1 3
#define MLKEM_DU 10
#define MLKEM_DV 4
#define MLKEM_POLYCOMPRESSEDBYTES_DV MLKEM_POLYCOMPRESSEDBYTES_D4
#define MLKEM_POLYCOMPRESSEDBYTES_DU MLKEM_POLYCOMPRESSEDBYTES_D10
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#elif MLKEM_K == 3
#define MLKEM_LVL 768
#define MLKEM_ETA1 2
#define MLKEM_DU 10
#define MLKEM_DV 4
#define MLKEM_POLYCOMPRESSEDBYTES_DV MLKEM_POLYCOMPRESSEDBYTES_D4
#define MLKEM_POLYCOMPRESSEDBYTES_DU MLKEM_POLYCOMPRESSEDBYTES_D10
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#elif MLKEM_K == 4
#define MLKEM_LVL 1024
#define MLKEM_ETA1 2
#define MLKEM_DU 11
#define MLKEM_DV 5
#define MLKEM_POLYCOMPRESSEDBYTES_DV MLKEM_POLYCOMPRESSEDBYTES_D5
#define MLKEM_POLYCOMPRESSEDBYTES_DU MLKEM_POLYCOMPRESSEDBYTES_D11
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#endif /* MLKEM_K == 4 */

#define MLKEM_ETA2 2

#define MLKEM_INDCPA_MSGBYTES (MLKEM_SYMBYTES)
#define MLKEM_INDCPA_PUBLICKEYBYTES (MLKEM_POLYVECBYTES + MLKEM_SYMBYTES)
#define MLKEM_INDCPA_SECRETKEYBYTES (MLKEM_POLYVECBYTES)
#define MLKEM_INDCPA_BYTES \
  (MLKEM_POLYVECCOMPRESSEDBYTES_DU + MLKEM_POLYCOMPRESSEDBYTES_DV)

#define MLKEM_INDCCA_PUBLICKEYBYTES (MLKEM_INDCPA_PUBLICKEYBYTES)
/* 32 bytes of additional space to save H(pk) */
#define MLKEM_INDCCA_SECRETKEYBYTES                            \
  (MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES + \
   2 * MLKEM_SYMBYTES)
#define MLKEM_INDCCA_CIPHERTEXTBYTES (MLKEM_INDCPA_BYTES)

#endif /* !MLK_PARAMS_H */
