/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../mlkem/kem.h"
#include "../mlkem/randombytes.h"
#include "../mlkem/sampling.h"
#include "hal.h"

#include "../mlkem/arith_backend.h"
#include "../mlkem/fips202/fips202.h"
#include "../mlkem/fips202/keccakf1600.h"
#include "../mlkem/indcpa.h"
#include "../mlkem/poly.h"
#include "../mlkem/poly_k.h"

#define NWARMUP 50
#define NITERATIONS 300
#define NTESTS 20

static int cmp_uint64_t(const void *a, const void *b)
{
  return (int)((*((const uint64_t *)a)) - (*((const uint64_t *)b)));
}

#define BENCH(txt, code)                                \
  for (i = 0; i < NTESTS; i++)                          \
  {                                                     \
    randombytes((uint8_t *)data0, sizeof(data0));       \
    randombytes((uint8_t *)data1, sizeof(data1));       \
    randombytes((uint8_t *)data2, sizeof(data2));       \
    randombytes((uint8_t *)data3, sizeof(data3));       \
    randombytes((uint8_t *)data4, sizeof(data4));       \
    for (j = 0; j < NWARMUP; j++)                       \
    {                                                   \
      code;                                             \
    }                                                   \
                                                        \
    t0 = get_cyclecounter();                            \
    for (j = 0; j < NITERATIONS; j++)                   \
    {                                                   \
      code;                                             \
    }                                                   \
    t1 = get_cyclecounter();                            \
    (cyc)[i] = t1 - t0;                                 \
  }                                                     \
  qsort((cyc), NTESTS, sizeof(uint64_t), cmp_uint64_t); \
  printf(txt " cycles=%" PRIu64 "\n", (cyc)[NTESTS >> 1] / NITERATIONS);

static int bench(void)
{
  MLK_ALIGN uint64_t data0[1024];
  MLK_ALIGN uint64_t data1[1024];
  MLK_ALIGN uint64_t data2[1024];
  MLK_ALIGN uint64_t data3[1024];
  MLK_ALIGN uint64_t data4[1024];
  uint8_t *seed[4];
  uint8_t nonce0 = 0, nonce1 = 1, nonce2 = 2, nonce3 = 3;
  uint64_t cyc[NTESTS];

  unsigned i, j;
  uint64_t t0, t1;

  seed[0] = (uint8_t *)data1;
  seed[1] = (uint8_t *)data2;
  seed[2] = (uint8_t *)data3;
  seed[3] = (uint8_t *)data4;

  BENCH("keccak-f1600-x1", mlk_keccakf1600_permute(data0))
  BENCH("keccak-f1600-x4", mlk_keccakf1600x4_permute(data0))
  BENCH("mlk_poly_rej_uniform",
        mlk_poly_rej_uniform((mlk_poly *)data0, (uint8_t *)data1))
  BENCH("mlk_poly_rej_uniform_x4",
        mlk_poly_rej_uniform_x4((mlk_poly *)data0, seed))

  /* mlk_poly */
  /* mlk_poly_compress_du */
  BENCH("mlk_poly_compress_du",
        mlk_poly_compress_du((uint8_t *)data0, (mlk_poly *)data1))

  /* mlk_poly_decompress_du */
  BENCH("mlk_poly_decompress_du",
        mlk_poly_decompress_du((mlk_poly *)data0, (uint8_t *)data1))

  /* mlk_poly_compress_dv */
  BENCH("mlk_poly_compress_dv",
        mlk_poly_compress_dv((uint8_t *)data0, (mlk_poly *)data1))

  /* mlk_poly_decompress_dv */
  BENCH("mlk_poly_decompress_dv",
        mlk_poly_decompress_dv((mlk_poly *)data0, (uint8_t *)data1))

  /* mlk_poly_tobytes */
  BENCH("mlk_poly_tobytes",
        mlk_poly_tobytes((uint8_t *)data0, (mlk_poly *)data1))

  /* mlk_poly_frombytes */
  BENCH("mlk_poly_frombytes",
        mlk_poly_frombytes((mlk_poly *)data0, (uint8_t *)data1))

  /* mlk_poly_frommsg */
  BENCH("mlk_poly_frommsg",
        mlk_poly_frommsg((mlk_poly *)data0, (uint8_t *)data1))

  /* mlk_poly_tomsg */
  BENCH("mlk_poly_tomsg", mlk_poly_tomsg((uint8_t *)data0, (mlk_poly *)data1))

  /* mlk_poly_getnoise_eta1_4x */
  BENCH("mlk_poly_getnoise_eta1_4x",
        mlk_poly_getnoise_eta1_4x((mlk_poly *)data0, (mlk_poly *)data1,
                                  (mlk_poly *)data2, (mlk_poly *)data3,
                                  (uint8_t *)data4, nonce0, nonce1, nonce2,
                                  nonce3))

#if MLKEM_K == 2 || MLKEM_K == 4
  /* mlk_poly_getnoise_eta2 */
  BENCH("mlk_poly_getnoise_eta2",
        mlk_poly_getnoise_eta2((mlk_poly *)data0, (uint8_t *)data1, nonce0))
#endif

#if MLKEM_K == 2
  /* mlk_poly_getnoise_eta1122_4x */
  BENCH("mlk_poly_getnoise_eta1122_4x",
        mlk_poly_getnoise_eta1122_4x((mlk_poly *)data0, (mlk_poly *)data1,
                                     (mlk_poly *)data2, (mlk_poly *)data3,
                                     (uint8_t *)data4, nonce0, nonce1, nonce2,
                                     nonce3))
#endif

  /* mlk_poly_tomont */
  BENCH("mlk_poly_tomont", mlk_poly_tomont((mlk_poly *)data0))

  /* mlk_poly_mulcache_compute */
  BENCH(
      "mlk_poly_mulcache_compute",
      mlk_poly_mulcache_compute((mlk_poly_mulcache *)data0, (mlk_poly *)data1))

  /* mlk_poly_reduce */
  BENCH("mlk_poly_reduce", mlk_poly_reduce((mlk_poly *)data0))

  /* mlk_poly_add */
  BENCH("mlk_poly_add", mlk_poly_add((mlk_poly *)data0, (mlk_poly *)data1))

  /* mlk_poly_sub */
  BENCH("mlk_poly_sub", mlk_poly_sub((mlk_poly *)data0, (mlk_poly *)data1))

  /* mlk_polyvec */
  /* mlk_polyvec_compress_du */
  BENCH("mlk_polyvec_compress_du",
        mlk_polyvec_compress_du((uint8_t *)data0, (mlk_polyvec *)data1))

  /* mlk_polyvec_decompress_du */
  BENCH("mlk_polyvec_decompress_du",
        mlk_polyvec_decompress_du((mlk_polyvec *)data0, (uint8_t *)data1))

  /* mlk_polyvec_tobytes */
  BENCH("mlk_polyvec_tobytes",
        mlk_polyvec_tobytes((uint8_t *)data0, (mlk_polyvec *)data1))

  /* mlk_polyvec_frombytes */
  BENCH("mlk_polyvec_frombytes",
        mlk_polyvec_frombytes((mlk_polyvec *)data0, (uint8_t *)data1))

  /* mlk_polyvec_ntt */
  BENCH("mlk_polyvec_ntt", mlk_polyvec_ntt((mlk_polyvec *)data0))

  /* mlk_polyvec_invntt_tomont */
  BENCH("mlk_polyvec_invntt_tomont",
        mlk_polyvec_invntt_tomont((mlk_polyvec *)data0))

  /* mlk_polyvec_basemul_acc_montgomery_cached */
  BENCH("mlk_polyvec_basemul_acc_montgomery_cached",
        mlk_polyvec_basemul_acc_montgomery_cached(
            (mlk_poly *)data0, (mlk_polyvec *)data1, (mlk_polyvec *)data2,
            (mlk_polyvec_mulcache *)data3))

  /* mlk_polyvec_mulcache_compute */
  BENCH("mlk_polyvec_mulcache_compute",
        mlk_polyvec_mulcache_compute((mlk_polyvec_mulcache *)data0,
                                     (mlk_polyvec *)data1))

  /* mlk_polyvec_reduce */
  BENCH("mlk_polyvec_reduce", mlk_polyvec_reduce((mlk_polyvec *)data0))

  /* mlk_polyvec_add */
  BENCH("mlk_polyvec_add",
        mlk_polyvec_add((mlk_polyvec *)data0, (mlk_polyvec *)data1))

  /* mlk_polyvec_tomont */
  BENCH("mlk_polyvec_tomont", mlk_polyvec_tomont((mlk_polyvec *)data0))

  /* indcpa */
  /* mlk_gen_matrix */
  BENCH("mlk_gen_matrix",
        mlk_gen_matrix((mlk_polyvec *)data0, (uint8_t *)data1, 0))


#if defined(MLK_ARITH_BACKEND_AARCH64_CLEAN)
  BENCH("ntt-clean", mlk_ntt_asm_clean((int16_t *)data0, (int16_t *)data1,
                                       (int16_t *)data2));
  BENCH("intt-clean", mlk_intt_asm_clean((int16_t *)data0, (int16_t *)data1,
                                         (int16_t *)data2));
  BENCH("mlk_poly-reduce-clean", mlk_poly_reduce_asm_clean((int16_t *)data0));
  BENCH("mlk_poly-tomont-clean", mlk_poly_tomont_asm_clean((int16_t *)data0));
  BENCH("mlk_poly-tobytes-clean",
        mlk_poly_tobytes_asm_clean((uint8_t *)data0, (int16_t *)data1));
  BENCH(
      "mlk_poly-mulcache-compute-clean",
      mlk_poly_mulcache_compute_asm_clean((int16_t *)data0, (int16_t *)data1,
                                          (int16_t *)data2, (int16_t *)data3));
#if MLKEM_K == 2
  BENCH("mlk_polyvec-basemul-acc-montgomery-cached-asm-clean",
        mlk_polyvec_basemul_acc_montgomery_cached_asm_k2_clean(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#elif MLKEM_K == 3
  BENCH("mlk_polyvec-basemul-acc-montgomery-cached-asm-clean",
        mlk_polyvec_basemul_acc_montgomery_cached_asm_k3_clean(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#elif MLKEM_K == 4
  BENCH("mlk_polyvec-basemul-acc-montgomery-cached-asm-clean",
        mlk_polyvec_basemul_acc_montgomery_cached_asm_k4_clean(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#endif
#endif /* MLK_ARITH_BACKEND_AARCH64_CLEAN */

#if defined(MLK_ARITH_BACKEND_AARCH64_OPT)
  BENCH("ntt-opt",
        mlk_ntt_asm_opt((int16_t *)data0, (int16_t *)data1, (int16_t *)data2));
  BENCH("intt-opt",
        mlk_intt_asm_opt((int16_t *)data0, (int16_t *)data1, (int16_t *)data2));
  BENCH("mlk_poly-reduce-opt", mlk_poly_reduce_asm_opt((int16_t *)data0));
  BENCH("mlk_poly-tomont-opt", mlk_poly_tomont_asm_opt((int16_t *)data0));
  BENCH("mlk_poly-mulcache-compute-opt",
        mlk_poly_mulcache_compute_asm_opt((int16_t *)data0, (int16_t *)data1,
                                          (int16_t *)data2, (int16_t *)data3));
#if MLKEM_K == 2
  BENCH("mlk_polyvec-basemul-acc-montgomery-cached-asm-opt",
        mlk_polyvec_basemul_acc_montgomery_cached_asm_k2_opt(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#elif MLKEM_K == 3
  BENCH("mlk_polyvec-basemul-acc-montgomery-cached-asm-opt",
        mlk_polyvec_basemul_acc_montgomery_cached_asm_k3_opt(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#elif MLKEM_K == 4
  BENCH("mlk_polyvec-basemul-acc-montgomery-cached-asm-opt",
        mlk_polyvec_basemul_acc_montgomery_cached_asm_k4_opt(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#endif
#endif /* MLK_ARITH_BACKEND_AARCH64_OPT */

  return 0;
}

int main(void)
{
  enable_cyclecounter();
  bench();
  disable_cyclecounter();

  return 0;
}
