/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "kem.h"

static void test_keygen_only(void)
{
  unsigned char pk[MLKEM_INDCCA_PUBLICKEYBYTES];
  unsigned char sk[MLKEM_INDCCA_SECRETKEYBYTES];

  /* Only call keypair - this is what we're measuring */
  /* Uses the notrandombytes implementation for deterministic randomness */
  int ret = crypto_kem_keypair(pk, sk);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}

static void test_encaps_only(void)
{
  unsigned char pk[MLKEM_INDCCA_PUBLICKEYBYTES] = {0};
  unsigned char ct[MLKEM_INDCCA_CIPHERTEXTBYTES];
  unsigned char ss[MLKEM_SSBYTES];

  /* Only call encaps - this is what we're measuring */
  /* pk is zero-initialized (invalid key, but OK for stack measurement) */
  int ret = crypto_kem_enc(ct, ss, pk);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}

static void test_decaps_only(void)
{
  unsigned char sk[MLKEM_INDCCA_SECRETKEYBYTES] = {0};
  unsigned char ct[MLKEM_INDCCA_CIPHERTEXTBYTES] = {0};
  unsigned char ss[MLKEM_SSBYTES];

  /* Only call decaps - this is what we're measuring */
  /* sk and ct are zero-initialized (invalid, but OK for stack measurement) */
  int ret = crypto_kem_dec(ss, ct, sk);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}

int main(int argc, char *argv[])
{
  if (argc != 2)
  {
    fprintf(stderr, "Usage: %s <keygen|encaps|decaps>\n", argv[0]);
    return 1;
  }

  if (strcmp(argv[1], "keygen") == 0)
  {
    test_keygen_only();
  }
  else if (strcmp(argv[1], "encaps") == 0)
  {
    test_encaps_only();
  }
  else if (strcmp(argv[1], "decaps") == 0)
  {
    test_decaps_only();
  }
  else
  {
    fprintf(stderr, "Unknown test: %s\n", argv[1]);
    return 1;
  }

  return 0;
}
