/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "expected_test_vectors_multilevel.h"
#include "mlkem_native_all.h"
#include "test_only_rng/notrandombytes.h"

#define CHECK(x)                                              \
  do                                                          \
  {                                                           \
    int rc;                                                   \
    rc = (x);                                                 \
    if (!rc)                                                  \
    {                                                         \
      fprintf(stderr, "ERROR (%s,%d)\n", __FILE__, __LINE__); \
      return 1;                                               \
    }                                                         \
  } while (0)

/* Keygen examples */

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
static int example_mlkem512_keygen(void)
{
  uint8_t pk[MLKEM512_PUBLICKEYBYTES];
  uint8_t sk[MLKEM512_SECRETKEYBYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("  Generating keypair (randomized)... ");
  CHECK(mlkem512_keypair(pk, sk) == 0);
  CHECK(memcmp(pk, test_vector_pk_512, MLKEM512_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk_512, MLKEM512_SECRETKEYBYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("  Generating keypair (deterministic)... ");
  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);
  CHECK(mlkem512_keypair_derand(pk, sk, coins) == 0);
  CHECK(memcmp(pk, test_vector_pk_512, MLKEM512_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk_512, MLKEM512_SECRETKEYBYTES) == 0);
  printf("DONE\n");
  return 0;
}

static int example_mlkem768_keygen(void)
{
  uint8_t pk[MLKEM768_PUBLICKEYBYTES];
  uint8_t sk[MLKEM768_SECRETKEYBYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("  Generating keypair (randomized)... ");
  CHECK(mlkem768_keypair(pk, sk) == 0);
  CHECK(memcmp(pk, test_vector_pk_768, MLKEM768_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk_768, MLKEM768_SECRETKEYBYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("  Generating keypair (deterministic)... ");
  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);
  CHECK(mlkem768_keypair_derand(pk, sk, coins) == 0);
  CHECK(memcmp(pk, test_vector_pk_768, MLKEM768_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk_768, MLKEM768_SECRETKEYBYTES) == 0);
  printf("DONE\n");
  return 0;
}

static int example_mlkem1024_keygen(void)
{
  uint8_t pk[MLKEM1024_PUBLICKEYBYTES];
  uint8_t sk[MLKEM1024_SECRETKEYBYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("  Generating keypair (randomized)... ");
  CHECK(mlkem1024_keypair(pk, sk) == 0);
  CHECK(memcmp(pk, test_vector_pk_1024, MLKEM1024_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk_1024, MLKEM1024_SECRETKEYBYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("  Generating keypair (deterministic)... ");
  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);
  CHECK(mlkem1024_keypair_derand(pk, sk, coins) == 0);
  CHECK(memcmp(pk, test_vector_pk_1024, MLKEM1024_PUBLICKEYBYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk_1024, MLKEM1024_SECRETKEYBYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_KEYPAIR_API */
static int example_mlkem512_keygen(void)
{
  printf("  Generating keypair... SKIPPED (keygen API disabled)\n");
  return 0;
}
static int example_mlkem768_keygen(void)
{
  printf("  Generating keypair... SKIPPED (keygen API disabled)\n");
  return 0;
}
static int example_mlkem1024_keygen(void)
{
  printf("  Generating keypair... SKIPPED (keygen API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_KEYPAIR_API */

/* Encaps examples */

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static int example_mlkem512_encaps(void)
{
  uint8_t ct[MLKEM512_CIPHERTEXTBYTES];
  uint8_t ss[MLKEM512_BYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("  Encaps (randomized)... ");
  CHECK(mlkem512_enc(ct, ss, test_vector_pk_512) == 0);
  CHECK(memcmp(ct, test_vector_ct_512, MLKEM512_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss_512, MLKEM512_BYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("  Encaps (deterministic)... ");
  CHECK(mlkem512_enc_derand(ct, ss, test_vector_pk_512, test_vector_m) == 0);
  CHECK(memcmp(ct, test_vector_ct_512, MLKEM512_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss_512, MLKEM512_BYTES) == 0);
  printf("DONE\n");
  return 0;
}

static int example_mlkem768_encaps(void)
{
  uint8_t ct[MLKEM768_CIPHERTEXTBYTES];
  uint8_t ss[MLKEM768_BYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("  Encaps (randomized)... ");
  CHECK(mlkem768_enc(ct, ss, test_vector_pk_768) == 0);
  CHECK(memcmp(ct, test_vector_ct_768, MLKEM768_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss_768, MLKEM768_BYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("  Encaps (deterministic)... ");
  CHECK(mlkem768_enc_derand(ct, ss, test_vector_pk_768, test_vector_m) == 0);
  CHECK(memcmp(ct, test_vector_ct_768, MLKEM768_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss_768, MLKEM768_BYTES) == 0);
  printf("DONE\n");
  return 0;
}

static int example_mlkem1024_encaps(void)
{
  uint8_t ct[MLKEM1024_CIPHERTEXTBYTES];
  uint8_t ss[MLKEM1024_BYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("  Encaps (randomized)... ");
  CHECK(mlkem1024_enc(ct, ss, test_vector_pk_1024) == 0);
  CHECK(memcmp(ct, test_vector_ct_1024, MLKEM1024_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss_1024, MLKEM1024_BYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("  Encaps (deterministic)... ");
  CHECK(mlkem1024_enc_derand(ct, ss, test_vector_pk_1024, test_vector_m) == 0);
  CHECK(memcmp(ct, test_vector_ct_1024, MLKEM1024_CIPHERTEXTBYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss_1024, MLKEM1024_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_ENCAPS_API */
static int example_mlkem512_encaps(void)
{
  printf("  Encaps... SKIPPED (encaps API disabled)\n");
  return 0;
}
static int example_mlkem768_encaps(void)
{
  printf("  Encaps... SKIPPED (encaps API disabled)\n");
  return 0;
}
static int example_mlkem1024_encaps(void)
{
  printf("  Encaps... SKIPPED (encaps API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_ENCAPS_API */

/* Decaps examples */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static int example_mlkem512_decaps(void)
{
  uint8_t ss[MLKEM512_BYTES];

  printf("  Decaps... ");
  CHECK(mlkem512_dec(ss, test_vector_ct_512, test_vector_sk_512) == 0);
  CHECK(memcmp(ss, test_vector_ss_512, MLKEM512_BYTES) == 0);
  printf("DONE\n");
  return 0;
}

static int example_mlkem768_decaps(void)
{
  uint8_t ss[MLKEM768_BYTES];

  printf("  Decaps... ");
  CHECK(mlkem768_dec(ss, test_vector_ct_768, test_vector_sk_768) == 0);
  CHECK(memcmp(ss, test_vector_ss_768, MLKEM768_BYTES) == 0);
  printf("DONE\n");
  return 0;
}

static int example_mlkem1024_decaps(void)
{
  uint8_t ss[MLKEM1024_BYTES];

  printf("  Decaps... ");
  CHECK(mlkem1024_dec(ss, test_vector_ct_1024, test_vector_sk_1024) == 0);
  CHECK(memcmp(ss, test_vector_ss_1024, MLKEM1024_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_DECAPS_API */
static int example_mlkem512_decaps(void)
{
  printf("  Decaps... SKIPPED (decaps API disabled)\n");
  return 0;
}
static int example_mlkem768_decaps(void)
{
  printf("  Decaps... SKIPPED (decaps API disabled)\n");
  return 0;
}
static int example_mlkem1024_decaps(void)
{
  printf("  Decaps... SKIPPED (decaps API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_DECAPS_API */

int main(void)
{
  int r = 0;

  printf("ML-KEM multilevel_build Example\n");
  printf("======================\n\n");

  printf("ML-KEM-512\n");
  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();
  r |= example_mlkem512_keygen();
  /* WARNING: Test-only
   * Normally, you would seed a PRNG _once_ with trustworthy entropy
   * and not reseed it afterwards. Here, we reseed to make tests
   * independent and reproducible. */
  randombytes_reset();
  r |= example_mlkem512_encaps();
  r |= example_mlkem512_decaps();

  printf("\nML-KEM-768\n");
  randombytes_reset();
  r |= example_mlkem768_keygen();
  randombytes_reset();
  r |= example_mlkem768_encaps();
  r |= example_mlkem768_decaps();

  printf("\nML-KEM-1024\n");
  randombytes_reset();
  r |= example_mlkem1024_keygen();
  randombytes_reset();
  r |= example_mlkem1024_encaps();
  r |= example_mlkem1024_decaps();

  if (r)
  {
    return 1;
  }

  printf("\nAll tests passed!\n");
  return 0;
}
