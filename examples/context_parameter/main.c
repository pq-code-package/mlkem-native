/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include <string.h>

/* Import public mlkem-native API. This also pulls in example_context.h,
 * which mlkem_native_config.h includes for the context parameter type. */
#include "expected_test_vectors.h"
#include "mlkem_native/mlkem_native.h"
#include "test_only_rng/notrandombytes.h"

/* Convenience abbreviations for the key and ciphertext sizes.
 *
 * Ordinarily you know the parameter set you're working with, so you would
 * just use the level-specific constants directly, e.g. MLKEM512_PUBLICKEYBYTES,
 * MLKEM768_CIPHERTEXTBYTES, or MLKEM1024_SECRETKEYBYTES.
 *
 * These examples, however, are compiled for all three parameter sets (512, 768,
 * 1024), so we keep things generic by deriving the sizes from the configured
 * MLK_CONFIG_PARAMETER_SET. */
#define MLKEM_PK_BYTES MLKEM_PUBLICKEYBYTES(MLK_CONFIG_PARAMETER_SET)
#define MLKEM_SK_BYTES MLKEM_SECRETKEYBYTES(MLK_CONFIG_PARAMETER_SET)
#define MLKEM_CT_BYTES MLKEM_CIPHERTEXTBYTES(MLK_CONFIG_PARAMETER_SET)

/* Size of the region the bump allocator hands out.
 *
 * MLK_TOTAL_ALLOC_{512,768,1024} is published by mlkem_native.h precisely for
 * this purpose: it is the maximum accumulated MLK_ALLOC usage across key
 * generation, encapsulation and decapsulation, and it already accounts for the
 * alignment rounding the allocator applies. So this buffer is exactly large
 * enough, and no operation can run out of memory. */
#if MLK_CONFIG_PARAMETER_SET == 512
#define EXAMPLE_ALLOC_SIZE MLK_TOTAL_ALLOC_512
#elif MLK_CONFIG_PARAMETER_SET == 768
#define EXAMPLE_ALLOC_SIZE MLK_TOTAL_ALLOC_768
#else
#define EXAMPLE_ALLOC_SIZE MLK_TOTAL_ALLOC_1024
#endif

static EXAMPLE_ALIGN uint8_t alloc_buffer[EXAMPLE_ALLOC_SIZE];

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

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
static int example_keygen(example_context *context)
{
  uint8_t pk[MLKEM_PK_BYTES];
  uint8_t sk[MLKEM_SK_BYTES];
  uint8_t coins[2 * MLKEM_SYMBYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("Generating keypair (randomized)... ");
  CHECK(mlkem_keypair(pk, sk, context) == 0);
  CHECK(memcmp(pk, test_vector_pk, MLKEM_PK_BYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk, MLKEM_SK_BYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("Generating keypair (deterministic)... ");
  memcpy(coins, test_vector_d, MLKEM_SYMBYTES);
  memcpy(coins + MLKEM_SYMBYTES, test_vector_z, MLKEM_SYMBYTES);
  CHECK(mlkem_keypair_derand(pk, sk, coins, context) == 0);
  CHECK(memcmp(pk, test_vector_pk, MLKEM_PK_BYTES) == 0);
  CHECK(memcmp(sk, test_vector_sk, MLKEM_SK_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_KEYPAIR_API */
static int example_keygen(example_context *context)
{
  (void)context;
  printf("Generating keypair... SKIPPED (keygen API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_KEYPAIR_API */

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static int example_encaps(example_context *context)
{
  uint8_t ct[MLKEM_CT_BYTES];
  uint8_t ss[MLKEM_BYTES];

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
  printf("Encaps (randomized)... ");
  CHECK(mlkem_enc(ct, ss, test_vector_pk, context) == 0);
  CHECK(memcmp(ct, test_vector_ct, MLKEM_CT_BYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss, MLKEM_BYTES) == 0);
  printf("DONE\n");
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

  printf("Encaps (deterministic)... ");
  CHECK(mlkem_enc_derand(ct, ss, test_vector_pk, test_vector_m, context) == 0);
  CHECK(memcmp(ct, test_vector_ct, MLKEM_CT_BYTES) == 0);
  CHECK(memcmp(ss, test_vector_ss, MLKEM_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_ENCAPS_API */
static int example_encaps(example_context *context)
{
  (void)context;
  printf("Encaps... SKIPPED (encaps API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static int example_decaps(example_context *context)
{
  uint8_t ss[MLKEM_BYTES];

  printf("Decaps... ");
  CHECK(mlkem_dec(ss, test_vector_ct, test_vector_sk, context) == 0);
  CHECK(memcmp(ss, test_vector_ss, MLKEM_BYTES) == 0);
  printf("DONE\n");
  return 0;
}
#else  /* !MLK_CONFIG_NO_DECAPS_API */
static int example_decaps(example_context *context)
{
  (void)context;
  printf("Decaps... SKIPPED (decaps API disabled)\n");
  return 0;
}
#endif /* MLK_CONFIG_NO_DECAPS_API */

int main(void)
{
  int r = 0;
  example_context context;

  printf("ML-KEM-%d, %d byte allocation buffer\n", MLK_CONFIG_PARAMETER_SET,
         (int)EXAMPLE_ALLOC_SIZE);
  example_context_init(&context, alloc_buffer, sizeof(alloc_buffer));

  /* WARNING: Test-only
   * Normally, you would seed a PRNG _once_ with trustworthy entropy and not
   * reseed it afterwards. Here, we reseed before each API call to make each
   * test independent and reproducible even when some API is disabled. */
  randombytes_reset();
  r |= example_keygen(&context);
  CHECK(context.used == 0);
  randombytes_reset();
  r |= example_encaps(&context);
  CHECK(context.used == 0);
  r |= example_decaps(&context);
  CHECK(context.used == 0);

  return r;
}
