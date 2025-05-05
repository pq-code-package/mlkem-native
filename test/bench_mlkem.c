/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../mlkem/common.h"
#include "../mlkem/kem.h"
#include "../mlkem/randombytes.h"
#include "hal.h"

#define CRYPTO_PUBLICKEYBYTES MLKEM_INDCCA_PUBLICKEYBYTES
#define CRYPTO_SECRETKEYBYTES MLKEM_INDCCA_SECRETKEYBYTES
#define CRYPTO_CIPHERTEXTBYTES MLKEM_INDCCA_CIPHERTEXTBYTES
#define CRYPTO_BYTES MLKEM_SYMBYTES

#define NWARMUP 50
#define NITERATIONS 300
#define NTESTS 500

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

static int cmp_uint64_t(const void *a, const void *b)
{
  return (int)((*((const uint64_t *)a)) - (*((const uint64_t *)b)));
}

static void print_median(const char *txt, uint64_t cyc[NTESTS])
{
  printf("%14s cycles = %" PRIu64 "\n", txt, cyc[NTESTS >> 1] / NITERATIONS);
}

static int percentiles[] = {1, 10, 20, 30, 40, 50, 60, 70, 80, 90, 99};

static void print_percentile_legend(void)
{
  unsigned i;
  printf("%25s", "percentile");
  for (i = 0; i < sizeof(percentiles) / sizeof(percentiles[0]); i++)
  {
    printf("%7d", percentiles[i]);
  }
  printf("\n");
}

static void print_percentiles(const char *txt, uint64_t cyc[NTESTS])
{
  unsigned i;
  printf("%14s percentiles:", txt);
  for (i = 0; i < sizeof(percentiles) / sizeof(percentiles[0]); i++)
  {
    printf("%7" PRIu64, (cyc)[NTESTS * percentiles[i] / 100] / NITERATIONS);
  }
  printf("\n");
}

static int bench(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  unsigned char kg_rand[2 * CRYPTO_BYTES], enc_rand[CRYPTO_BYTES];
  uint64_t cycles_kg[NTESTS], cycles_enc[NTESTS], cycles_dec[NTESTS];


  mlk_public_key pks;
  mlk_secret_key sks;
  uint64_t cycles_kg_struct[NTESTS];
  uint64_t cycles_pk_marshal[NTESTS];
  uint64_t cycles_sk_marshal[NTESTS];

  uint64_t cycles_pk_parse[NTESTS];
  uint64_t cycles_enc_struct[NTESTS];

  uint64_t cycles_sk_parse[NTESTS];
  uint64_t cycles_dec_struct[NTESTS];

  unsigned i, j;
  uint64_t t0, t1;


  for (i = 0; i < NTESTS; i++)
  {
    int ret = 0;
    randombytes(kg_rand, 2 * CRYPTO_BYTES);
    randombytes(enc_rand, CRYPTO_BYTES);

    /* Key-pair generation */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_keypair_derand(pk, sk, kg_rand);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_keypair_derand(pk, sk, kg_rand);
    }
    t1 = get_cyclecounter();
    cycles_kg[i] = t1 - t0;


    /* Encapsulation */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_enc_derand(ct, key_a, pk, enc_rand);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_enc_derand(ct, key_a, pk, enc_rand);
    }
    t1 = get_cyclecounter();
    cycles_enc[i] = t1 - t0;

    /* Decapsulation */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_dec(key_b, ct, sk);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_dec(key_b, ct, sk);
    }
    t1 = get_cyclecounter();
    cycles_dec[i] = t1 - t0;

    CHECK(ret == 0);
    CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) == 0);


    /* Key-pair generation */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_keypair_derand_struct(&pks, &sks, kg_rand);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_keypair_derand_struct(&pks, &sks, kg_rand);
    }
    t1 = get_cyclecounter();
    cycles_kg_struct[i] = t1 - t0;


    /* Marshal public key */
    for (j = 0; j < NWARMUP; j++)
    {
      crypto_kem_marshal_pk(pk, &pks);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      crypto_kem_marshal_pk(pk, &pks);
    }
    t1 = get_cyclecounter();
    cycles_pk_marshal[i] = t1 - t0;

    /* Marshal secret key */
    for (j = 0; j < NWARMUP; j++)
    {
      crypto_kem_marshal_sk(sk, &sks);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      crypto_kem_marshal_sk(sk, &sks);
    }
    t1 = get_cyclecounter();
    cycles_sk_marshal[i] = t1 - t0;


    /* pk parse */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_parse_pk(&pks, pk);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_parse_pk(&pks, pk);
    }
    t1 = get_cyclecounter();
    cycles_pk_parse[i] = t1 - t0;


    /* encaps */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_enc_derand_struct(ct, key_a, &pks, enc_rand);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_enc_derand_struct(ct, key_a, &pks, enc_rand);
    }
    t1 = get_cyclecounter();
    cycles_enc_struct[i] = t1 - t0;


    /* sk prase */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_parse_sk(&sks, sk);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_parse_sk(&sks, sk);
    }
    t1 = get_cyclecounter();
    cycles_sk_parse[i] = t1 - t0;


    /* decaps */
    for (j = 0; j < NWARMUP; j++)
    {
      ret |= crypto_kem_dec_struct(key_b, ct, &sks);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++)
    {
      ret |= crypto_kem_dec_struct(key_b, ct, &sks);
    }
    t1 = get_cyclecounter();
    cycles_dec_struct[i] = t1 - t0;

    CHECK(ret == 0);
    CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) == 0);
  }

  qsort(cycles_kg, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_enc, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_dec, NTESTS, sizeof(uint64_t), cmp_uint64_t);

  qsort(cycles_kg_struct, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_pk_marshal, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_sk_marshal, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_pk_parse, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_enc_struct, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_sk_parse, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_dec_struct, NTESTS, sizeof(uint64_t), cmp_uint64_t);


  print_median("keypair", cycles_kg);
  print_median("encaps", cycles_enc);
  print_median("decaps", cycles_dec);

  print_median("keypair_struct", cycles_kg_struct);
  print_median("marshal_pk", cycles_pk_marshal);
  print_median("marshal_sk", cycles_sk_marshal);
  print_median("parse_pk", cycles_pk_parse);
  print_median("encaps_struct", cycles_enc_struct);
  print_median("parse_sk", cycles_sk_parse);
  print_median("decaps_struct", cycles_dec_struct);

  printf("\n");

  print_percentile_legend();

  print_percentiles("keypair", cycles_kg);
  print_percentiles("encaps", cycles_enc);
  print_percentiles("decaps", cycles_dec);

  print_percentiles("keypair_struct", cycles_kg_struct);
  print_percentiles("marshal_pk", cycles_pk_marshal);
  print_percentiles("marshal_sk", cycles_sk_marshal);
  print_percentiles("parse_pk", cycles_pk_parse);
  print_percentiles("encaps_struct", cycles_enc_struct);
  print_percentiles("parse_sk", cycles_sk_parse);
  print_percentiles("decaps_struct", cycles_dec_struct);

  return 0;
}

int main(void)
{
  enable_cyclecounter();
  bench();
  disable_cyclecounter();

  return 0;
}
