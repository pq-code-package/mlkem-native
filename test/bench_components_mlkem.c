/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../mlkem/kem.h"
#include "../mlkem/randombytes.h"
#include "../mlkem/rej_uniform.h"
#include "hal.h"

#include "../mlkem/arith_backend.h"
#include "../mlkem/fips202/fips202.h"
#include "../mlkem/fips202/keccakf1600.h"
#include "../mlkem/indcpa.h"
#include "../mlkem/poly.h"
#include "../mlkem/poly_k.h"

#define NWARMUP 50
#define NITERERATIONS 300
#define NTESTS 200

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
    for (j = 0; j < NITERERATIONS; j++)                 \
    {                                                   \
      code;                                             \
    }                                                   \
    t1 = get_cyclecounter();                            \
    (cyc)[i] = t1 - t0;                                 \
  }                                                     \
  qsort((cyc), NTESTS, sizeof(uint64_t), cmp_uint64_t); \
  printf(txt " cycles=%" PRIu64 "\n", (cyc)[NTESTS >> 1] / NITERERATIONS);

static int bench(void)
{
  ALIGN uint64_t data0[1024];
  ALIGN uint64_t data1[1024];
  ALIGN uint64_t data2[1024];
  ALIGN uint64_t data3[1024];
  ALIGN uint64_t data4[1024];
  uint8_t nonce0 = 0, nonce1 = 1, nonce2 = 2, nonce3 = 3;
  uint64_t cyc[NTESTS];

  unsigned i, j;
  uint64_t t0, t1;

  BENCH("keccak-f1600-x1", KeccakF1600_StatePermute(data0))
  BENCH("keccak-f1600-x4", KeccakF1600x4_StatePermute(data0))
  BENCH("rej_uniform (bulk)",
        rej_uniform((int16_t *)data0, MLKEM_N, 0, (const uint8_t *)data1,
                    3 * SHAKE128_RATE))
  BENCH("rej_uniform (residue)",
        rej_uniform((int16_t *)data0, MLKEM_N / 2, 0, (const uint8_t *)data1,
                    1 * SHAKE128_RATE))

  /* poly */
  /* poly_compress_du */
  BENCH("poly_compress_du", poly_compress_du((uint8_t *)data0, (poly *)data1))

  /* poly_decompress_du */
  BENCH("poly_decompress_du",
        poly_decompress_du((poly *)data0, (uint8_t *)data1))

  /* poly_compress_dv */
  BENCH("poly_compress_dv", poly_compress_dv((uint8_t *)data0, (poly *)data1))

  /* poly_decompress_dv */
  BENCH("poly_decompress_dv",
        poly_decompress_dv((poly *)data0, (uint8_t *)data1))

  /* poly_tobytes */
  BENCH("poly_tobytes", poly_tobytes((uint8_t *)data0, (poly *)data1))

  /* poly_frombytes */
  BENCH("poly_frombytes", poly_frombytes((poly *)data0, (uint8_t *)data1))

  /* poly_frommsg */
  BENCH("poly_frommsg", poly_frommsg((poly *)data0, (uint8_t *)data1))

  /* poly_tomsg */
  BENCH("poly_tomsg", poly_tomsg((uint8_t *)data0, (poly *)data1))

  /* poly_getnoise_eta1_4x */
  BENCH("poly_getnoise_eta1_4x",
        poly_getnoise_eta1_4x((poly *)data0, (poly *)data1, (poly *)data2,
                              (poly *)data3, (uint8_t *)data4, nonce0, nonce1,
                              nonce2, nonce3))

#if MLKEM_K == 2 || MLKEM_K == 4
  /* poly_getnoise_eta2 */
  BENCH("poly_getnoise_eta2",
        poly_getnoise_eta2((poly *)data0, (uint8_t *)data1, nonce0))
#endif

#if MLKEM_K == 2
  /* poly_getnoise_eta1122_4x */
  BENCH("poly_getnoise_eta1122_4x",
        poly_getnoise_eta1122_4x((poly *)data0, (poly *)data1, (poly *)data2,
                                 (poly *)data3, (uint8_t *)data4, nonce0,
                                 nonce1, nonce2, nonce3))
#endif

  /* poly_basemul_montgomery_cached */
  BENCH("poly_basemul_montgomery_cached",
        poly_basemul_montgomery_cached((poly *)data0, (poly *)data1,
                                       (poly *)data2, (poly_mulcache *)data3))

  /* poly_tomont */
  BENCH("poly_tomont", poly_tomont((poly *)data0))

  /* poly_mulcache_compute */
  BENCH("poly_mulcache_compute",
        poly_mulcache_compute((poly_mulcache *)data0, (poly *)data1))

  /* poly_reduce */
  BENCH("poly_reduce", poly_reduce((poly *)data0))

  /* poly_add */
  BENCH("poly_add", poly_add((poly *)data0, (poly *)data1))

  /* poly_sub */
  BENCH("poly_sub", poly_sub((poly *)data0, (poly *)data1))

  /* polyvec */
  /* polyvec_compress_du */
  BENCH("polyvec_compress_du",
        polyvec_compress_du((uint8_t *)data0, (polyvec *)data1))

  /* polyvec_decompress_du */
  BENCH("polyvec_decompress_du",
        polyvec_decompress_du((polyvec *)data0, (uint8_t *)data1))

  /* polyvec_tobytes */
  BENCH("polyvec_tobytes", polyvec_tobytes((uint8_t *)data0, (polyvec *)data1))

  /* polyvec_frombytes */
  BENCH("polyvec_frombytes",
        polyvec_frombytes((polyvec *)data0, (uint8_t *)data1))

  /* polyvec_ntt */
  BENCH("polyvec_ntt", polyvec_ntt((polyvec *)data0))

  /* polyvec_invntt_tomont */
  BENCH("polyvec_invntt_tomont", polyvec_invntt_tomont((polyvec *)data0))

  /* polyvec_basemul_acc_montgomery_cached */
  BENCH("polyvec_basemul_acc_montgomery_cached",
        polyvec_basemul_acc_montgomery_cached((poly *)data0, (polyvec *)data1,
                                              (polyvec *)data2,
                                              (polyvec_mulcache *)data3))

  /* polyvec_mulcache_compute */
  BENCH("polyvec_mulcache_compute",
        polyvec_mulcache_compute((polyvec_mulcache *)data0, (polyvec *)data1))

  /* polyvec_reduce */
  BENCH("polyvec_reduce", polyvec_reduce((polyvec *)data0))

  /* polyvec_add */
  BENCH("polyvec_add", polyvec_add((polyvec *)data0, (polyvec *)data1))

  /* polyvec_tomont */
  BENCH("polyvec_tomont", polyvec_tomont((polyvec *)data0))

  /* indcpa */
  /* gen_matrix */
  BENCH("gen_matrix", gen_matrix((polyvec *)data0, (uint8_t *)data1, 0))


#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN)
  BENCH("ntt-clean",
        ntt_asm_clean((int16_t *)data0, (int16_t *)data1, (int16_t *)data2));
  BENCH("intt-clean",
        intt_asm_clean((int16_t *)data0, (int16_t *)data1, (int16_t *)data2));
  BENCH("poly-reduce-clean", poly_reduce_asm_clean((int16_t *)data0));
  BENCH("poly-tomont-clean", poly_tomont_asm_clean((int16_t *)data0));
  BENCH("poly-tobytes-clean",
        poly_tobytes_asm_clean((uint8_t *)data0, (int16_t *)data1));
  BENCH("poly-mulcache-compute-clean",
        poly_mulcache_compute_asm_clean((int16_t *)data0, (int16_t *)data1,
                                        (int16_t *)data2, (int16_t *)data3));
  BENCH("poly-basemul-acc-montgomery-clean",
        polyvec_basemul_acc_montgomery_cached_asm_clean(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#endif /* MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN */

#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT)
  BENCH("ntt-opt",
        ntt_asm_opt((int16_t *)data0, (int16_t *)data1, (int16_t *)data2));
  BENCH("intt-opt",
        intt_asm_opt((int16_t *)data0, (int16_t *)data1, (int16_t *)data2));
  BENCH("poly-reduce-opt", poly_reduce_asm_opt((int16_t *)data0));
  BENCH("poly-tomont-opt", poly_tomont_asm_opt((int16_t *)data0));
  BENCH("poly-mulcache-compute-opt",
        poly_mulcache_compute_asm_opt((int16_t *)data0, (int16_t *)data1,
                                      (int16_t *)data2, (int16_t *)data3));
  BENCH("poly-basemul-acc-montgomery-opt",
        polyvec_basemul_acc_montgomery_cached_asm_opt(
            (int16_t *)data0, (int16_t *)data1, (int16_t *)data2,
            (int16_t *)data3));
#endif /* MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT */

  return 0;
}

int main(void)
{
  enable_cyclecounter();
  bench();
  disable_cyclecounter();

  return 0;
}
