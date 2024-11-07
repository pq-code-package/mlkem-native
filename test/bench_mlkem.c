// SPDX-License-Identifier: Apache-2.0
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "hal.h"
#include "kem.h"
#include "randombytes.h"

#define NWARMUP 50
#define NITERATIONS 300
#define NTESTS 500

static int cmp_uint64_t(const void *a, const void *b) {
  return (int)((*((const uint64_t *)a)) - (*((const uint64_t *)b)));
}

static void print_median(const char *txt, uint64_t cyc[NTESTS]) {
  printf("%14s cycles = %" PRIu64 "\n", txt, cyc[NTESTS >> 1] / NITERATIONS);
}

static int percentiles[] = {1, 10, 20, 30, 40, 50, 60, 70, 80, 90, 99};

static void print_percentile_legend(void) {
  printf("%27s", "percentile");
  for (unsigned i = 0; i < sizeof(percentiles) / sizeof(percentiles[0]); i++)
    printf("%7d", percentiles[i]);
  printf("\n");
}

static void print_percentiles(const char *txt, uint64_t cyc[NTESTS]) {
  printf("%14s percentiles:", txt);
  for (unsigned i = 0; i < sizeof(percentiles) / sizeof(percentiles[0]); i++)
    printf("%7" PRIu64, (cyc)[NTESTS * percentiles[i] / 100] / NITERATIONS);
  printf("\n");
}

static int bench(void) {
  mlkem_public_key pk;
  mlkem_secret_key sk;
  uint8_t pks[CRYPTO_PUBLICKEYBYTES];
  uint8_t sks[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  unsigned char kg_rand[2 * CRYPTO_BYTES], enc_rand[CRYPTO_BYTES];
  uint64_t cycles_kg[NTESTS], cycles_enc[NTESTS], cycles_dec[NTESTS];
  uint64_t cycles_ser_sk[NTESTS], cycles_deser_sk[NTESTS],
      cycles_ser_pk[NTESTS], cycles_deser_pk[NTESTS];

  unsigned int i, j;
  uint64_t t0, t1;


  for (i = 0; i < NTESTS; i++) {
    randombytes(kg_rand, 2 * CRYPTO_BYTES);
    randombytes(enc_rand, CRYPTO_BYTES);

    // Key-pair generation
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_keypair_derand(&pk, &sk, kg_rand);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++) {
      crypto_kem_keypair_derand(&pk, &sk, kg_rand);
    }
    t1 = get_cyclecounter();
    cycles_kg[i] = t1 - t0;


    // Serialize secret key
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_serialize_sk(sks, &sk);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++) {
      crypto_kem_serialize_sk(sks, &sk);
    }
    t1 = get_cyclecounter();
    cycles_ser_sk[i] = t1 - t0;



    // Serialize public key
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_serialize_pk(pks, &pk);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++) {
      crypto_kem_serialize_pk(pks, &pk);
    }
    t1 = get_cyclecounter();
    cycles_ser_pk[i] = t1 - t0;


    // Deserialize public key
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_deserialize_pk(&pk, pks);
    }

    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++) {
      crypto_kem_deserialize_pk(&pk, pks);
    }
    t1 = get_cyclecounter();
    cycles_deser_pk[i] = t1 - t0;


    // Encapsulation
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_enc_derand(ct, key_a, &pk, enc_rand);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++) {
      crypto_kem_enc_derand(ct, key_a, &pk, enc_rand);
    }
    t1 = get_cyclecounter();
    cycles_enc[i] = t1 - t0;

    // Deserialize secret key
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_deserialize_sk(&sk, sks);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++) {
      crypto_kem_deserialize_sk(&sk, sks);
    }
    t1 = get_cyclecounter();
    cycles_deser_sk[i] = t1 - t0;


    // Decapsulation
    for (j = 0; j < NWARMUP; j++) {
      crypto_kem_dec(key_b, ct, &sk);
    }
    t0 = get_cyclecounter();
    for (j = 0; j < NITERATIONS; j++) {
      crypto_kem_dec(key_b, ct, &sk);
    }
    t1 = get_cyclecounter();
    cycles_dec[i] = t1 - t0;


    if (memcmp(key_a, key_b, CRYPTO_BYTES)) {
      printf("ERROR keys\n");
      return 1;
    }
  }

  qsort(cycles_kg, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_enc, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_dec, NTESTS, sizeof(uint64_t), cmp_uint64_t);

  qsort(cycles_ser_sk, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_ser_pk, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_deser_sk, NTESTS, sizeof(uint64_t), cmp_uint64_t);
  qsort(cycles_deser_pk, NTESTS, sizeof(uint64_t), cmp_uint64_t);

  print_median("keypair", cycles_kg);
  print_median("serialize_pk", cycles_ser_pk);
  print_median("serialize_sk", cycles_ser_sk);

  print_median("deserialize_pk", cycles_deser_pk);
  print_median("encaps", cycles_enc);

  print_median("deserialize_sk", cycles_deser_sk);
  print_median("decaps", cycles_dec);

  printf("\n");

  print_percentile_legend();

  print_percentiles("keypair", cycles_kg);
  print_percentiles("serialize_pk", cycles_ser_pk);
  print_percentiles("serialize_sk", cycles_ser_sk);

  print_percentiles("deserialize_pk", cycles_deser_pk);
  print_percentiles("encaps", cycles_enc);

  print_percentiles("deserialize_sk", cycles_deser_sk);
  print_percentiles("decaps", cycles_dec);

  return 0;
}

int main(void) {
  enable_cyclecounter();
  bench();
  disable_cyclecounter();

  return 0;
}
