/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "../mlkem/fips202/fips202.h"
#include "../mlkem/mlkem_native.h"

#if defined(_WIN64) || defined(_WIN32)
#include <fcntl.h>
#include <io.h>
#endif

#define NTESTS 1000

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

static void print_hex(const char *label, const uint8_t *data, size_t size)
{
  size_t i;
  printf("%s = ", label);
  for (i = 0; i < size; i++)
  {
    printf("%02x", data[i]);
  }
  printf("\n");
}

int main(void)
{
  unsigned i;
  MLK_ALIGN uint8_t coins[3 * CRYPTO_SYMBYTES];
  MLK_ALIGN uint8_t pk[CRYPTO_PUBLICKEYBYTES];
  MLK_ALIGN uint8_t sk[CRYPTO_SECRETKEYBYTES];
  MLK_ALIGN uint8_t ct[CRYPTO_CIPHERTEXTBYTES];
  MLK_ALIGN uint8_t ss1[CRYPTO_BYTES];
  MLK_ALIGN uint8_t ss2[CRYPTO_BYTES];

  const uint8_t seed[64] = {
      32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
      48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
      64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
      80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
  };

#if defined(_WIN64) || defined(_WIN32)
  /* Disable automatic CRLF conversion on Windows to match testvector hashes */
  _setmode(_fileno(stdout), _O_BINARY);
#endif


  mlk_shake256(coins, sizeof(coins), seed, sizeof(seed));

  for (i = 0; i < NTESTS; i++)
  {
    mlk_shake256(coins, sizeof(coins), coins, sizeof(coins));

    CHECK(crypto_kem_keypair_derand(pk, sk, coins) == 0);
    print_hex("pk", pk, sizeof(pk));
    print_hex("sk", sk, sizeof(sk));

    CHECK(crypto_kem_enc_derand(ct, ss1, pk, coins + 2 * MLKEM_SYMBYTES) == 0);
    print_hex("ct", ct, sizeof(ct));

    CHECK(crypto_kem_dec(ss2, ct, sk) == 0);
    CHECK(memcmp(ss1, ss2, sizeof(ss1)) == 0);

    print_hex("ss", ss1, sizeof(ss1));
  }

  return 0;
}
