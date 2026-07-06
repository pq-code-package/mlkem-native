/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mlkem_native.h"

static void print_info(void)
{
#if !defined(MLK_CONFIG_NO_KEYPAIR_API) && \
    !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("keygen\n");
#endif
#if !defined(MLK_CONFIG_NO_ENCAPS_API) && !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("encaps\n");
#endif
#if !defined(MLK_CONFIG_NO_DECAPS_API)
  printf("decaps\n");
#endif
}

#if !defined(MLK_CONFIG_NO_KEYPAIR_API) && \
    !defined(MLK_CONFIG_NO_RANDOMIZED_API)
static void test_keygen_only(void)
{
  unsigned char pk[CRYPTO_PUBLICKEYBYTES];
  unsigned char sk[CRYPTO_SECRETKEYBYTES];

  /* Only call keypair - this is what we're measuring */
  /* Uses the notrandombytes implementation for deterministic randomness */
  int ret = crypto_kem_keypair(pk, sk);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}
#endif /* !MLK_CONFIG_NO_KEYPAIR_API && !MLK_CONFIG_NO_RANDOMIZED_API */

#if !defined(MLK_CONFIG_NO_ENCAPS_API) && !defined(MLK_CONFIG_NO_RANDOMIZED_API)
static void test_encaps_only(void)
{
  unsigned char pk[CRYPTO_PUBLICKEYBYTES] = {0};
  unsigned char ct[CRYPTO_CIPHERTEXTBYTES];
  unsigned char ss[CRYPTO_BYTES];

  /* Only call encaps - this is what we're measuring */
  /* pk is zero-initialized (invalid key, but OK for stack measurement) */
  int ret = crypto_kem_enc(ct, ss, pk);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}
#endif /* !MLK_CONFIG_NO_ENCAPS_API && !MLK_CONFIG_NO_RANDOMIZED_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static void test_decaps_only(void)
{
  unsigned char sk[CRYPTO_SECRETKEYBYTES] = {0};
  unsigned char ct[CRYPTO_CIPHERTEXTBYTES] = {0};
  unsigned char ss[CRYPTO_BYTES];

  /* Only call decaps - this is what we're measuring */
  /* sk and ct are zero-initialized (invalid, but OK for stack measurement) */
  int ret = crypto_kem_dec(ss, ct, sk);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}
#endif /* !MLK_CONFIG_NO_DECAPS_API */

/* Prototype for a re-#define'd main, to satisfy -Wmissing-prototypes. */
#if defined(main)
int main(int argc, char *argv[]);
#endif
int main(int argc, char *argv[])
{
  if (argc != 2)
  {
    fprintf(stderr, "Usage: %s <--info|keygen|encaps|decaps>\n", argv[0]);
    return 1;
  }

  if (strcmp(argv[1], "--info") == 0)
  {
    print_info();
  }
  else if (strcmp(argv[1], "keygen") == 0)
  {
#if !defined(MLK_CONFIG_NO_KEYPAIR_API) && \
    !defined(MLK_CONFIG_NO_RANDOMIZED_API)
    test_keygen_only();
#else
    printf("SKIPPED (keygen API disabled)\n");
#endif
  }
  else if (strcmp(argv[1], "encaps") == 0)
  {
#if !defined(MLK_CONFIG_NO_ENCAPS_API) && !defined(MLK_CONFIG_NO_RANDOMIZED_API)
    test_encaps_only();
#else
    printf("SKIPPED (encaps API disabled)\n");
#endif
  }
  else if (strcmp(argv[1], "decaps") == 0)
  {
#if !defined(MLK_CONFIG_NO_DECAPS_API)
    test_decaps_only();
#else
    printf("SKIPPED (decaps API disabled)\n");
#endif
  }
  else
  {
    fprintf(stderr, "Unknown test: %s\n", argv[1]);
    return 1;
  }

  return 0;
}
