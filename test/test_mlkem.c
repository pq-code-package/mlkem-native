/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../mlkem/src/compress.h"
#include "../mlkem/src/poly_k.h"

#include "../mlkem/mlkem_native.h"
#include "notrandombytes/notrandombytes.h"

#ifndef NTESTS
#define NTESTS 1000
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


static int test_keys(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];

  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Alice uses Bobs response to get her shared key */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);

  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, CRYPTO_BYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, CRYPTO_BYTES);

  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) == 0);
  return 0;
}

static int test_invalid_pk(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_b[CRYPTO_BYTES];
  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* set first public key coefficient to 4095 (0xFFF) */
  pk[0] = 0xFF;
  pk[1] |= 0x0F;
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) != 0);
  return 0;
}

static int test_invalid_sk_a(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Replace first part of secret key with random values */
  randombytes(sk, 10);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to wrong sk */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);
  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, CRYPTO_BYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, CRYPTO_BYTES);

  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) != 0);
  return 0;
}

static int test_invalid_sk_b(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Replace H(pk) with radom values; */
  randombytes(sk + CRYPTO_SECRETKEYBYTES - 64, 32);
  /* Alice uses Bobs response to get her shared key
   * This should fail due to the input validation */
  CHECK(crypto_kem_dec(key_a, ct, sk) != 0);
  return 0;
}

static int test_invalid_ciphertext(void)
{
  uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  uint8_t sk[CRYPTO_SECRETKEYBYTES];
  uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  uint8_t key_a[CRYPTO_BYTES];
  uint8_t key_b[CRYPTO_BYTES];
  uint8_t b;
  size_t pos;

  do
  {
    randombytes(&b, sizeof(uint8_t));
  } while (!b);
  randombytes((uint8_t *)&pos, sizeof(size_t));

  /* Alice generates a public key */
  CHECK(crypto_kem_keypair(pk, sk) == 0);
  /* Bob derives a secret key and creates a response */
  CHECK(crypto_kem_enc(ct, key_b, pk) == 0);
  /* Change some byte in the ciphertext (i.e., encapsulated key) */
  ct[pos % CRYPTO_CIPHERTEXTBYTES] ^= b;
  /* Alice uses Bobs response to get her shared key */
  CHECK(crypto_kem_dec(key_a, ct, sk) == 0);
  /* mark as defined, so we can compare */
  MLK_CT_TESTING_DECLASSIFY(key_a, CRYPTO_BYTES);
  MLK_CT_TESTING_DECLASSIFY(key_b, CRYPTO_BYTES);
  CHECK(memcmp(key_a, key_b, CRYPTO_BYTES) != 0);
  return 0;
}

/* This test invokes the polynomial (de)compression routines
 * with minimally sized buffers. When run with address sanitization,
 * this ensures that no buffer overflow is happening. This is of interest
 * because the compressed buffers sometimes have unaligned lengths and
 * are therefore at risk of being overflowed by vectorized code. */
static int test_poly_compress_no_overflow(void)
{
#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || (MLKEM_K == 2 || MLKEM_K == 3)
  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d4(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d4(&s, r);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d10(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d10(&s, r);
  }
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == 3 */

#if defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4
  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d5(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d5(&s, r);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11];
    mlk_poly s;
    memset((uint8_t *)&s, 0, sizeof(s));
    mlk_poly_compress_d11(r, &s);
  }

  {
    uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11];
    mlk_poly s;
    memset(r, 0, sizeof(r));
    mlk_poly_decompress_d11(&s, r);
  }
#endif /* MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4 */

  return 0;
}

#if defined(MLK_USE_NATIVE_POLY_REDUCE) ||                                  \
    defined(MLK_USE_NATIVE_POLY_TOMONT) || defined(MLK_USE_NATIVE_NTT) ||   \
    defined(MLK_USE_NATIVE_INTT) || defined(MLK_USE_NATIVE_POLY_TOBYTES) || \
    defined(MLK_USE_NATIVE_POLY_FROMBYTES) ||                               \
    defined(MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)

/* Backend unit test helper functions */
static void print_u8_array(const char *label, const uint8_t *array, size_t len)
{
  size_t i;
  fprintf(stderr, "%s:\n", label);
  for (i = 0; i < len; i++)
  {
    if (i % 16 == 0)
    {
      fprintf(stderr, "  ");
    }
    fprintf(stderr, "%4d", array[i]);
    if (i % 16 == 15)
    {
      fprintf(stderr, "\n");
    }
    else
    {
      fprintf(stderr, " ");
    }
  }
  if (len % 16 != 0)
  {
    fprintf(stderr, "\n");
  }
}

static void print_i16_array(const char *label, const int16_t *array, size_t len)
{
  size_t i;
  fprintf(stderr, "%s:\n", label);
  for (i = 0; i < len; i++)
  {
    if (i % 16 == 0)
    {
      fprintf(stderr, "  ");
    }
    fprintf(stderr, "%6d", array[i]);
    if (i % 16 == 15)
    {
      fprintf(stderr, "\n");
    }
    else
    {
      fprintf(stderr, " ");
    }
  }
  if (len % 16 != 0)
  {
    fprintf(stderr, "\n");
  }
}

static void generate_i16_array_zeros(int16_t *data, size_t len)
{
  memset(data, 0, len * sizeof(int16_t));
}

static void generate_i16_array_single(int16_t *data, size_t len, size_t pos,
                                      int16_t value)
{
  memset(data, 0, len * sizeof(int16_t));
  data[pos] = value;
}

static void generate_i16_array_random(int16_t *data, size_t len)
{
  size_t i;

  randombytes((uint8_t *)data, len * sizeof(int16_t));
  for (i = 0; i < len; i++)
  {
    data[i] = data[i] % MLKEM_Q;
  }
}

static int compare_u8_arrays(const uint8_t *a, const uint8_t *b, size_t len,
                             const char *test_name)
{
  size_t i;
  for (i = 0; i < len; i++)
  {
    if (a[i] != b[i])
    {
      fprintf(stderr, "FAIL: %s\n", test_name);
      fprintf(stderr,
              "  First difference at index %zu: native=%d, reference=%d\n", i,
              a[i], b[i]);
      print_u8_array("Native result", a, len);
      print_u8_array("Reference result", b, len);
      return 0;
    }
  }
  return 1;
}

static int compare_i16_arrays(const int16_t *a, const int16_t *b, size_t len,
                              const char *test_name, const int16_t *input)
{
  size_t i;
  for (i = 0; i < len; i++)
  {
    if (a[i] != b[i])
    {
      fprintf(stderr, "FAIL: %s\n", test_name);
      fprintf(stderr,
              "  First difference at index %zu: native=%d, reference=%d\n", i,
              a[i], b[i]);
      if (input)
      {
        print_i16_array("Input", input, len);
      }
      print_i16_array("Native result", a, len);
      print_i16_array("Reference result", b, len);
      return 0;
    }
  }
  return 1;
}

#ifdef MLK_USE_NATIVE_POLY_REDUCE
static int test_poly_reduce_core(const int16_t *input, const char *test_name)
{
  int16_t native_result[MLKEM_N];
  mlk_poly ref_poly;
  int native_ret;

  memcpy(native_result, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

  native_ret = mlk_poly_reduce_native(native_result);
  if (native_ret == MLK_NATIVE_FUNC_FALLBACK)
  {
    return 0; /* Skip if not supported */
  }

  mlk_poly_reduce_c(&ref_poly);
  CHECK(compare_i16_arrays(native_result, ref_poly.coeffs, MLKEM_N, test_name,
                           NULL));
  return 0;
}

static int test_native_poly_reduce(void)
{
  int16_t test_data[MLKEM_N];
  int pos;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_poly_reduce_core(test_data, "poly_reduce_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, pos, MLKEM_Q - 1);
    CHECK(test_poly_reduce_core(test_data, "poly_reduce_single") == 0);
  }

  generate_i16_array_random(test_data, MLKEM_N);
  CHECK(test_poly_reduce_core(test_data, "poly_reduce_random") == 0);

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_REDUCE */

#ifdef MLK_USE_NATIVE_POLY_TOMONT
static int test_poly_tomont_core(const int16_t *input, const char *test_name)
{
  int16_t native_result[MLKEM_N];
  mlk_poly ref_poly;
  int native_ret;

  memcpy(native_result, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

  native_ret = mlk_poly_tomont_native(native_result);
  if (native_ret == MLK_NATIVE_FUNC_FALLBACK)
  {
    return 0; /* Skip if not supported */
  }

  mlk_poly_tomont_c(&ref_poly);

  /* Normalize */
  mlk_poly_reduce_c(&ref_poly);
  mlk_poly_reduce_c((mlk_poly*) native_result);

  CHECK(compare_i16_arrays(native_result, ref_poly.coeffs, MLKEM_N, test_name,
                           NULL));
  return 0;
}

static int test_native_poly_tomont(void)
{
  int16_t test_data[MLKEM_N];
  int pos;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_poly_tomont_core(test_data, "poly_tomont_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, pos, MLKEM_Q - 1);
    CHECK(test_poly_tomont_core(test_data, "poly_tomont_single") == 0);
  }

  generate_i16_array_random(test_data, MLKEM_N);
  CHECK(test_poly_tomont_core(test_data, "poly_tomont_random") == 0);

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_TOMONT */

#ifdef MLK_USE_NATIVE_NTT
static int test_ntt_core(const int16_t *input, const char *test_name)
{
  int16_t native_result[MLKEM_N];
  mlk_poly ref_poly;
  int native_ret;

  fprintf(stderr, "NTT CORE TEST\n");

  memcpy(native_result, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

  native_ret = mlk_ntt_native(native_result);
  if (native_ret == MLK_NATIVE_FUNC_FALLBACK)
  {
    fprintf(stderr, "Skipping\n");
    return 0;
  }

  mlk_poly_ntt_c(&ref_poly);

#ifdef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
  mlk_poly_permute_bitrev_to_custom(ref_poly.coeffs);
#endif

  /* Normalize */
  mlk_poly_reduce_c(&ref_poly);
  mlk_poly_reduce_c((mlk_poly*) native_result);

  CHECK(compare_i16_arrays(native_result, ref_poly.coeffs, MLKEM_N, test_name,
                           input));
  return 0;
}

static int test_native_ntt(void)
{
  int16_t test_data[MLKEM_N];
  int pos;

  /* Use a more complex test that will expose the bug */
  generate_i16_array_random(test_data, MLKEM_N);
  CHECK(test_ntt_core(test_data, "ntt_complex") == 0);

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_ntt_core(test_data, "ntt_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, pos, MLKEM_Q - 1);
    CHECK(test_ntt_core(test_data, "ntt_single") == 0);
  }

  generate_i16_array_random(test_data, MLKEM_N);
  CHECK(test_ntt_core(test_data, "ntt_random") == 0);

  return 0;
}
#endif /* MLK_USE_NATIVE_NTT */

#ifdef MLK_USE_NATIVE_INTT
static int test_intt_core(const int16_t *input, const char *test_name)
{
  int16_t native_result[MLKEM_N];
  mlk_poly ref_poly;
  int native_ret;

  memcpy(native_result, input, MLKEM_N * sizeof(int16_t));
  memcpy(ref_poly.coeffs, input, MLKEM_N * sizeof(int16_t));

  native_ret = mlk_intt_native(native_result);
  if (native_ret == MLK_NATIVE_FUNC_FALLBACK)
  {
    return 0;
  }

  mlk_poly_invntt_tomont_c(&ref_poly);

  /* Normalize */
  mlk_poly_reduce_c(&ref_poly);
  mlk_poly_reduce_c((mlk_poly*) native_result);

  CHECK(compare_i16_arrays(native_result, ref_poly.coeffs, MLKEM_N, test_name,
                           NULL));
  return 0;
}

static int test_native_intt(void)
{
  int16_t test_data[MLKEM_N];
  int pos;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_intt_core(test_data, "intt_zeros") == 0);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, pos, MLKEM_Q - 1);
    CHECK(test_intt_core(test_data, "intt_single") == 0);
  }

  generate_i16_array_random(test_data, MLKEM_N);
  CHECK(test_intt_core(test_data, "intt_random") == 0);

  return 0;
}
#endif /* MLK_USE_NATIVE_INTT */

#ifdef MLK_USE_NATIVE_POLY_TOBYTES
static int test_poly_tobytes_core(const int16_t *input, const char *test_name)
{
  uint8_t native_result[MLKEM_POLYBYTES], ref_result[MLKEM_POLYBYTES];
  mlk_poly ref_poly;
  int16_t valid_input[MLKEM_N];
  int native_ret;
  int i;

  /* Ensure input is in valid range [0, MLKEM_Q-1] for tobytes */
  for (i = 0; i < MLKEM_N; i++)
  {
    valid_input[i] = ((input[i] % MLKEM_Q) + MLKEM_Q) % MLKEM_Q;
  }

  memcpy(ref_poly.coeffs, valid_input, MLKEM_N * sizeof(int16_t));

  native_ret = mlk_poly_tobytes_native(native_result, valid_input);
  if (native_ret == MLK_NATIVE_FUNC_FALLBACK)
  {
    return 0; /* Skip if not supported */
  }

  mlk_poly_tobytes_c(ref_result, &ref_poly);

  CHECK(
      compare_u8_arrays(native_result, ref_result, MLKEM_POLYBYTES, test_name));
  return 1;
}

static int test_native_poly_tobytes(void)
{
  int16_t test_data[MLKEM_N];
  int pos;

  generate_i16_array_zeros(test_data, MLKEM_N);
  CHECK(test_poly_tobytes_core(test_data, "poly_tobytes_zeros") == 1);

  for (pos = 0; pos < MLKEM_N; pos += MLKEM_N / 8)
  {
    generate_i16_array_single(test_data, MLKEM_N, pos, MLKEM_Q - 1);
    CHECK(test_poly_tobytes_core(test_data, "poly_tobytes_single") == 1);
  }

  generate_i16_array_random(test_data, MLKEM_N);
  CHECK(test_poly_tobytes_core(test_data, "poly_tobytes_random") == 1);

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_TOBYTES */

#ifdef MLK_USE_NATIVE_POLY_FROMBYTES
static int test_poly_frombytes_core(const uint8_t *input_bytes,
                                    const char *test_name)
{
  int16_t native_result[MLKEM_N];
  mlk_poly ref_poly;
  int native_ret;

  native_ret = mlk_poly_frombytes_native(native_result, input_bytes);
  if (native_ret == MLK_NATIVE_FUNC_FALLBACK)
  {
    return 0; /* Skip if not supported */
  }

  mlk_poly_frombytes_c(&ref_poly, input_bytes);
  CHECK(compare_i16_arrays(native_result, ref_poly.coeffs, MLKEM_N, test_name,
                           NULL));
  return 0;
}

static int test_native_poly_frombytes(void)
{
  uint8_t test_bytes[MLKEM_POLYBYTES];
  int16_t temp_data[MLKEM_POLYBYTES / 2];

  /* Test with zero bytes */
  memset(test_bytes, 0, MLKEM_POLYBYTES);
  CHECK(test_poly_frombytes_core(test_bytes, "poly_frombytes_zeros") == 0);

  /* Test with incremental bytes */
  generate_i16_array_zeros(temp_data, MLKEM_POLYBYTES / 2);
  generate_i16_array_random(temp_data, MLKEM_POLYBYTES / 2);
  memcpy(test_bytes, temp_data, MLKEM_POLYBYTES);
  CHECK(test_poly_frombytes_core(test_bytes, "poly_frombytes_incremental") ==
        0);

  /* Test with random bytes */
  generate_i16_array_random(temp_data, MLKEM_POLYBYTES / 2);
  memcpy(test_bytes, temp_data, MLKEM_POLYBYTES);
  CHECK(test_poly_frombytes_core(test_bytes, "poly_frombytes_random") == 0);

  return 0;
}
#endif /* MLK_USE_NATIVE_POLY_FROMBYTES */

#ifdef MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
static int test_polyvec_basemul_core(const int16_t *a, const int16_t *b,
                                     const int16_t *b_cache,
                                     const char *test_name)
{
  int16_t native_result[MLKEM_N];
  mlk_poly ref_result;
  mlk_polyvec ref_a, ref_b;
  mlk_polyvec_mulcache ref_cache;
  int native_ret;
  int i;

  /* Copy test data to reference structures */
  for (i = 0; i < MLKEM_K; i++)
  {
    memcpy(ref_a[i].coeffs, &a[i * MLKEM_N], MLKEM_N * sizeof(int16_t));
    memcpy(ref_b[i].coeffs, &b[i * MLKEM_N], MLKEM_N * sizeof(int16_t));
    memcpy(ref_cache[i].coeffs, &b_cache[i * (MLKEM_N / 2)],
           (MLKEM_N / 2) * sizeof(int16_t));
  }

#if MLKEM_K == 2
  native_ret = mlk_polyvec_basemul_acc_montgomery_cached_k2_native(
      native_result, a, b, b_cache);
#elif MLKEM_K == 3
  native_ret = mlk_polyvec_basemul_acc_montgomery_cached_k3_native(
      native_result, a, b, b_cache);
#elif MLKEM_K == 4
  native_ret = mlk_polyvec_basemul_acc_montgomery_cached_k4_native(
      native_result, a, b, b_cache);
#endif

  if (native_ret == MLK_NATIVE_FUNC_FALLBACK)
  {
    return 0; /* Skip if not supported */
  }

  mlk_polyvec_basemul_acc_montgomery_cached_c(&ref_result, ref_a, ref_b,
                                            ref_cache);

  /* Normalize */
  mlk_poly_reduce_c(&ref_result);
  mlk_poly_reduce_c((mlk_poly*) native_result);

  CHECK(compare_i16_arrays(native_result, ref_result.coeffs, MLKEM_N, test_name,
                           NULL));
  return 0;
}

static int test_native_polyvec_basemul(void)
{
  int16_t a[MLKEM_K * MLKEM_N];
  int16_t b[MLKEM_K * MLKEM_N];
  int16_t b_cache[MLKEM_K * (MLKEM_N / 2)];

  /* Test with zeros */
  generate_i16_array_zeros(a, MLKEM_K * MLKEM_N);
  generate_i16_array_zeros(b, MLKEM_K * MLKEM_N);
  generate_i16_array_zeros(b_cache, MLKEM_K * (MLKEM_N / 2));
  CHECK(test_polyvec_basemul_core(a, b, b_cache, "polyvec_basemul_zeros") == 0);

  /* Test with random data */
  generate_i16_array_random(a, MLKEM_K * MLKEM_N);
  generate_i16_array_random(b, MLKEM_K * MLKEM_N);
  generate_i16_array_random(b_cache, MLKEM_K * (MLKEM_N / 2));
  CHECK(test_polyvec_basemul_core(a, b, b_cache, "polyvec_basemul_random") ==
        0);

  return 0;
}
#endif /* MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

static int test_backend_units(void)
{
  /* Set fixed seed for reproducible tests */
  randombytes_reset();

#ifdef MLK_USE_NATIVE_POLY_REDUCE
  CHECK(test_native_poly_reduce() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLY_TOMONT
  CHECK(test_native_poly_tomont() == 0);
#endif

#ifdef MLK_USE_NATIVE_NTT
  CHECK(test_native_ntt() == 0);
#endif

#ifdef MLK_USE_NATIVE_INTT
  CHECK(test_native_intt() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLY_TOBYTES
  CHECK(test_native_poly_tobytes() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLY_FROMBYTES
  CHECK(test_native_poly_frombytes() == 0);
#endif

#ifdef MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
  CHECK(test_native_polyvec_basemul() == 0);
#endif

  return 0;
}

#endif /* MLK_USE_NATIVE_POLY_REDUCE || MLK_USE_NATIVE_POLY_TOMONT ||     \
          MLK_USE_NATIVE_NTT || MLK_USE_NATIVE_INTT ||                    \
          MLK_USE_NATIVE_POLY_TOBYTES || MLK_USE_NATIVE_POLY_FROMBYTES || \
          MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

int main(void)
{
  unsigned i;

  /* WARNING: Test-only
   * Normally, you would want to seed a PRNG with trustworthy entropy here. */
  randombytes_reset();

  /* Run backend unit tests first */
#if defined(MLK_USE_NATIVE_POLY_REDUCE) ||                                  \
    defined(MLK_USE_NATIVE_POLY_TOMONT) || defined(MLK_USE_NATIVE_NTT) ||   \
    defined(MLK_USE_NATIVE_INTT) || defined(MLK_USE_NATIVE_POLY_TOBYTES) || \
    defined(MLK_USE_NATIVE_POLY_FROMBYTES) ||                               \
    defined(MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
  CHECK(test_backend_units() == 0);
#endif /* MLK_USE_NATIVE_POLY_REDUCE || MLK_USE_NATIVE_POLY_TOMONT ||     \
          MLK_USE_NATIVE_NTT || MLK_USE_NATIVE_INTT ||                    \
          MLK_USE_NATIVE_POLY_TOBYTES || MLK_USE_NATIVE_POLY_FROMBYTES || \
          MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

  for (i = 0; i < NTESTS; i++)
  {
    CHECK(test_keys() == 0);
    CHECK(test_invalid_pk() == 0);
    CHECK(test_invalid_sk_a() == 0);
    CHECK(test_invalid_sk_b() == 0);
    CHECK(test_invalid_ciphertext() == 0);
    CHECK(test_poly_compress_no_overflow() == 0);
  }

  printf("CRYPTO_SECRETKEYBYTES:  %d\n", CRYPTO_SECRETKEYBYTES);
  printf("CRYPTO_PUBLICKEYBYTES:  %d\n", CRYPTO_PUBLICKEYBYTES);
  printf("CRYPTO_CIPHERTEXTBYTES: %d\n", CRYPTO_CIPHERTEXTBYTES);

  return 0;
}
