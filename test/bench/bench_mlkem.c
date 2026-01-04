/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../mlkem/src/common.h"
#include "../../mlkem/src/randombytes.h"
#include "hal.h"

#include "../../mlkem/mlkem_native.h"

#ifndef MLK_BENCHMARK_NWARMUP
#define MLK_BENCHMARK_NWARMUP 50
#endif
#ifndef MLK_BENCHMARK_NITERATIONS
#define MLK_BENCHMARK_NITERATIONS 300
#endif
#ifndef MLK_BENCHMARK_NTESTS
#define MLK_BENCHMARK_NTESTS 500
#endif

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

static void print_median(const char *txt, uint64_t cyc[MLK_BENCHMARK_NTESTS])
{
  printf("%10s cycles = %" PRIu64 "\n", txt,
         cyc[MLK_BENCHMARK_NTESTS >> 1] / MLK_BENCHMARK_NITERATIONS);
}

static int percentiles[] = {1, 10, 20, 30, 40, 50, 60, 70, 80, 90, 99};

static void print_percentile_legend(void)
{
  unsigned i;
  printf("%21s", "percentile");
  for (i = 0; i < sizeof(percentiles) / sizeof(percentiles[0]); i++)
  {
    printf("%9d", percentiles[i]);
  }
  printf("\n");
}

static void print_percentiles(const char *txt,
                              uint64_t cyc[MLK_BENCHMARK_NTESTS])
{
  unsigned i;
  printf("%10s percentiles:", txt);
  for (i = 0; i < sizeof(percentiles) / sizeof(percentiles[0]); i++)
  {
    printf("%9" PRIu64, (cyc)[MLK_BENCHMARK_NTESTS * percentiles[i] / 100] /
                            MLK_BENCHMARK_NITERATIONS);
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
  uint64_t cycles_kg[MLK_BENCHMARK_NTESTS], cycles_enc[MLK_BENCHMARK_NTESTS],
      cycles_dec[MLK_BENCHMARK_NTESTS];

  unsigned i, j;
  uint64_t t0, t1;


  for (i = 0; i < MLK_BENCHMARK_NTESTS; i++)
  {
    int ret = 0;
    CHECK(randombytes(kg_rand, 2 * CRYPTO_BYTES) == 0);
    CHECK(randombytes(enc_rand, CRYPTO_BYTES) == 0);

    /* Key-pair generation */
    for (j = 0; j < MLK_BENCHMARK_NWARMUP; j++)
    {
      ret |= crypto_kem_keypair_derand(pk, sk, kg_rand);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < MLK_BENCHMARK_NITERATIONS; j++)
    {
      ret |= crypto_kem_keypair_derand(pk, sk, kg_rand);
    }
    t1 = get_cyclecounter();
    cycles_kg[i] = t1 - t0;


    /* Encapsulation */
    for (j = 0; j < MLK_BENCHMARK_NWARMUP; j++)
    {
      ret |= crypto_kem_enc_derand(ct, key_a, pk, enc_rand);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < MLK_BENCHMARK_NITERATIONS; j++)
    {
      ret |= crypto_kem_enc_derand(ct, key_a, pk, enc_rand);
    }
    t1 = get_cyclecounter();
    cycles_enc[i] = t1 - t0;

    /* Decapsulation */
    for (j = 0; j < MLK_BENCHMARK_NWARMUP; j++)
    {
      ret |= crypto_kem_dec(key_b, ct, sk);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < MLK_BENCHMARK_NITERATIONS; j++)
    {
      ret |= crypto_kem_dec(key_b, ct, sk);
    }
    t1 = get_cyclecounter();
    cycles_dec[i] = t1 - t0;

    CHECK(ret == 0);
    CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) == 0);
  }

  qsort(cycles_kg, MLK_BENCHMARK_NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_enc, MLK_BENCHMARK_NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_dec, MLK_BENCHMARK_NTESTS, sizeof(uint64_t), cmp_uint64_t);

  print_median("keypair", cycles_kg);
  print_median("encaps", cycles_enc);
  print_median("decaps", cycles_dec);

  printf("\n");

  print_percentile_legend();

  print_percentiles("keypair", cycles_kg);
  print_percentiles("encaps", cycles_enc);
  print_percentiles("decaps", cycles_dec);

  return 0;
}

int main(void)
{
  enable_cyclecounter();
  bench();
  disable_cyclecounter();

  return 0;
}
