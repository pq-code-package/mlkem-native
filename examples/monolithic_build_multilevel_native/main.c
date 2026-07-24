/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mlkem_native_all.c"

#define MLK_CONFIG_CONSTANTS_ONLY
#include <mlkem_native.h>
#include "expected_test_vectors_multilevel.h"
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

/* Per-level test functions. Each block is guarded by the matching
 * reduced-API config so the multilevel example works with any subset
 * of enabled APIs. */

#define TEST_LEVEL_KEYGEN(LVL)                                                 \
  static int example_keygen_##LVL(void)                                        \
  {                                                                            \
    uint8_t pk[MLKEM##LVL##_PUBLICKEYBYTES];                                   \
    uint8_t sk[MLKEM##LVL##_SECRETKEYBYTES];                                   \
                                                                               \
    randombytes_reset();                                                       \
    printf("[MLKEM-" #LVL "] Generating keypair... ");                         \
    CHECK(mlkem##LVL##_keypair(pk, sk) == 0);                                  \
    CHECK(memcmp(pk, test_vector_pk_##LVL, MLKEM##LVL##_PUBLICKEYBYTES) == 0); \
    CHECK(memcmp(sk, test_vector_sk_##LVL, MLKEM##LVL##_SECRETKEYBYTES) == 0); \
    printf("DONE\n");                                                          \
    return 0;                                                                  \
  }

#define TEST_LEVEL_ENCAPS(LVL)                                              \
  static int example_encaps_##LVL(void)                                     \
  {                                                                         \
    uint8_t ct[MLKEM##LVL##_CIPHERTEXTBYTES];                               \
    uint8_t ss[MLKEM##LVL##_BYTES];                                         \
                                                                            \
    randombytes_reset();                                                    \
    printf("[MLKEM-" #LVL "] Encaps... ");                                  \
    CHECK(mlkem##LVL##_enc(ct, ss, test_vector_pk_##LVL) == 0);             \
    CHECK(memcmp(ct, test_vector_ct_##LVL, MLKEM##LVL##_CIPHERTEXTBYTES) == \
          0);                                                               \
    CHECK(memcmp(ss, test_vector_ss_##LVL, MLKEM##LVL##_BYTES) == 0);       \
    printf("DONE\n");                                                       \
    return 0;                                                               \
  }

#define TEST_LEVEL_DECAPS(LVL)                                                \
  static int example_decaps_##LVL(void)                                       \
  {                                                                           \
    uint8_t ss[MLKEM##LVL##_BYTES];                                           \
                                                                              \
    printf("[MLKEM-" #LVL "] Decaps... ");                                    \
    CHECK(mlkem##LVL##_dec(ss, test_vector_ct_##LVL, test_vector_sk_##LVL) == \
          0);                                                                 \
    CHECK(memcmp(ss, test_vector_ss_##LVL, MLKEM##LVL##_BYTES) == 0);         \
    printf("DONE\n");                                                         \
    return 0;                                                                 \
  }

#define TEST_LEVEL_SKIP(NAME, LVL, MSG)           \
  static int example_##NAME##_##LVL(void)         \
  {                                               \
    printf("[MLKEM-" #LVL "] " MSG " SKIPPED\n"); \
    return 0;                                     \
  }

#if !defined(MLK_CONFIG_NO_KEYPAIR_API) && \
    !defined(MLK_CONFIG_NO_RANDOMIZED_API)
TEST_LEVEL_KEYGEN(512)
TEST_LEVEL_KEYGEN(768)
TEST_LEVEL_KEYGEN(1024)
#else  /* !MLK_CONFIG_NO_KEYPAIR_API && !MLK_CONFIG_NO_RANDOMIZED_API */
TEST_LEVEL_SKIP(keygen, 512, "Generating keypair...")
TEST_LEVEL_SKIP(keygen, 768, "Generating keypair...")
TEST_LEVEL_SKIP(keygen, 1024, "Generating keypair...")
#endif /* !(!MLK_CONFIG_NO_KEYPAIR_API && !MLK_CONFIG_NO_RANDOMIZED_API) */

#if !defined(MLK_CONFIG_NO_ENCAPS_API) && !defined(MLK_CONFIG_NO_RANDOMIZED_API)
TEST_LEVEL_ENCAPS(512)
TEST_LEVEL_ENCAPS(768)
TEST_LEVEL_ENCAPS(1024)
#else
TEST_LEVEL_SKIP(encaps, 512, "Encaps...")
TEST_LEVEL_SKIP(encaps, 768, "Encaps...")
TEST_LEVEL_SKIP(encaps, 1024, "Encaps...")
#endif

#if !defined(MLK_CONFIG_NO_DECAPS_API)
TEST_LEVEL_DECAPS(512)
TEST_LEVEL_DECAPS(768)
TEST_LEVEL_DECAPS(1024)
#else
TEST_LEVEL_SKIP(decaps, 512, "Decaps...")
TEST_LEVEL_SKIP(decaps, 768, "Decaps...")
TEST_LEVEL_SKIP(decaps, 1024, "Decaps...")
#endif

int main(void)
{
  int r = 0;
  r |= example_keygen_512();
  r |= example_encaps_512();
  r |= example_decaps_512();
  r |= example_keygen_768();
  r |= example_encaps_768();
  r |= example_decaps_768();
  r |= example_keygen_1024();
  r |= example_encaps_1024();
  r |= example_decaps_1024();
  return r;
}
