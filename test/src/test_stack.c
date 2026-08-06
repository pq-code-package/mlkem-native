/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mlkem_native.h"
#include "test_namespace.h"

#include "../test_vectors/expected_test_vectors.h"

static void print_info(void)
{
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
  printf("keygen\n");
#endif
#if !defined(MLK_CONFIG_NO_ENCAPS_API)
  printf("encaps\n");
#endif
#if !defined(MLK_CONFIG_NO_DECAPS_API)
  printf("decaps\n");
#endif
}

/*
 * We measure the derandomized entry points rather than the randomized
 * wrappers: they are available in every configuration (no configuration
 * disables them), so the same measurements are taken under reduced-API
 * builds such as MLK_CONFIG_NO_RANDOMIZED_API. The randomized wrappers
 * merely add a coins buffer and a randombytes() call on top.
 */
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
static void test_keygen_only(void)
{
  unsigned char pk[MLKEM_PK_BYTES];
  unsigned char sk[MLKEM_SK_BYTES];
  unsigned char coins[2 * MLKEM_SYMBYTES] = {0};

  /* Only call keypair_derand - this is what we're measuring */
  /* coins is zero-initialized; the value is irrelevant for stack measurement */
  int ret = mlk_kem_keypair_derand(pk, sk, coins);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static void test_encaps_only(void)
{
  unsigned char pk[MLKEM_PK_BYTES] = {0};
  unsigned char ct[MLKEM_CT_BYTES];
  unsigned char ss[MLKEM_BYTES];
  unsigned char coins[MLKEM_SYMBYTES] = {0};

  /* Only call enc_derand - this is what we're measuring */
  /* pk and coins are zero-initialized (OK for stack measurement) */
  int ret = mlk_kem_enc_derand(ct, ss, pk, coins);
  (void)ret; /* Ignore return value - we only care about stack measurement */
}
#endif /* !MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static void test_decaps_only(void)
{
  unsigned char sk[MLKEM_SK_BYTES];
  unsigned char ct[MLKEM_CT_BYTES];
  unsigned char ss[MLKEM_BYTES];
  int ret;

  /* A valid sk is needed: mlk_kem_dec() returns on the H(ek) check
   * before decapsulating, leaving most of the work unmeasured. */
  memcpy(sk, test_vector_sk, sizeof(sk));
  memcpy(ct, test_vector_ct, sizeof(ct));

  /* Only call decaps - this is what we're measuring */
  ret = mlk_kem_dec(ss, ct, sk);
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
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
    test_keygen_only();
#else
    printf("SKIPPED (keygen API disabled)\n");
#endif
  }
  else if (strcmp(argv[1], "encaps") == 0)
  {
#if !defined(MLK_CONFIG_NO_ENCAPS_API)
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
