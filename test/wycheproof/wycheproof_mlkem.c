/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Wycheproof test driver for ML-KEM.
 *
 * Usage:
 *   wycheproof_mlkem{lvl} keygen_seed seed=HEX
 *   wycheproof_mlkem{lvl} encaps ek=HEX m=HEX
 *   wycheproof_mlkem{lvl} decaps dk=HEX c=HEX
 */

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../mlkem/src/common.h"
#include "../../mlkem/mlkem_native.h"

#define CHECK(x)                                              \
  do                                                          \
  {                                                           \
    int rc;                                                   \
    rc = (x);                                                 \
    if (!rc)                                                  \
    {                                                         \
      fprintf(stderr, "ERROR (%s,%d)\n", __FILE__, __LINE__); \
      exit(1);                                                \
    }                                                         \
  } while (0)

static unsigned char decode_hex_char(char hex)
{
  if (hex >= '0' && hex <= '9')
    return (unsigned char)(hex - '0');
  else if (hex >= 'A' && hex <= 'F')
    return (unsigned char)(10 + (unsigned char)(hex - 'A'));
  else if (hex >= 'a' && hex <= 'f')
    return (unsigned char)(10 + (unsigned char)(hex - 'a'));
  else
    return 0xFF;
}

static int decode_hex(const char *prefix, unsigned char *out, size_t out_len,
                      const char *hex)
{
  size_t i;
  size_t hex_len = strlen(hex);
  size_t prefix_len = strlen(prefix);

  if (hex_len < prefix_len + 1 || memcmp(prefix, hex, prefix_len) != 0 ||
      hex[prefix_len] != '=')
    return 1;

  hex += prefix_len + 1;
  hex_len -= prefix_len + 1;

  if (hex_len != 2 * out_len)
    return 1;

  for (i = 0; i < out_len; i++, hex += 2, out++)
  {
    unsigned hex0 = decode_hex_char(hex[0]);
    unsigned hex1 = decode_hex_char(hex[1]);
    if (hex0 == 0xFF || hex1 == 0xFF)
      return 1;
    *out = (unsigned char)((hex0 << 4) | hex1);
  }
  return 0;
}

static void print_hex(const char *name, const unsigned char *raw, size_t len)
{
  if (name != NULL)
    printf("%s=", name);
  for (; len > 0; len--, raw++)
    printf("%02X", *raw);
  printf("\n");
}

int main(int argc, char *argv[])
{
  if (argc < 2)
    goto usage;

  if (strcmp(argv[1], "keygen_seed") == 0)
  {
    /* keygen_seed seed=HEX (64 bytes = d || z) */
    unsigned char seed[2 * MLKEM_SYMBYTES];
    unsigned char ek[CRYPTO_PUBLICKEYBYTES];
    unsigned char dk[CRYPTO_SECRETKEYBYTES];

    if (argc != 3)
      goto usage;

    if (decode_hex("seed", seed, sizeof(seed), argv[2]) != 0)
    {
      printf("decode_error=1\n");
      return 0;
    }

    CHECK(crypto_kem_keypair_derand(ek, dk, seed) == 0);
    print_hex("ek", ek, sizeof(ek));
    print_hex("dk", dk, sizeof(dk));
  }
  else if (strcmp(argv[1], "encaps") == 0)
  {
    /* encaps ek=HEX m=HEX */
    unsigned char ek[CRYPTO_PUBLICKEYBYTES];
    unsigned char m[MLKEM_SYMBYTES];
    unsigned char ct[CRYPTO_CIPHERTEXTBYTES];
    unsigned char ss[CRYPTO_BYTES];

    if (argc != 4)
      goto usage;

    if (decode_hex("ek", ek, sizeof(ek), argv[2]) != 0 ||
        decode_hex("m", m, sizeof(m), argv[3]) != 0)
    {
      printf("decode_error=1\n");
      return 0;
    }

    CHECK(crypto_kem_enc_derand(ct, ss, ek, m) == 0);
    print_hex("c", ct, sizeof(ct));
    print_hex("K", ss, sizeof(ss));
  }
  else if (strcmp(argv[1], "decaps") == 0)
  {
    /* decaps dk=HEX c=HEX */
    unsigned char dk[CRYPTO_SECRETKEYBYTES];
    unsigned char c[CRYPTO_CIPHERTEXTBYTES];
    unsigned char ss[CRYPTO_BYTES];

    if (argc != 4)
      goto usage;

    if (decode_hex("dk", dk, sizeof(dk), argv[2]) != 0)
    {
      /* Incorrect dk length - report decode failure */
      printf("decode_error=1\n");
      return 0;
    }
    if (decode_hex("c", c, sizeof(c), argv[3]) != 0)
    {
      printf("decode_error=1\n");
      return 0;
    }

    CHECK(crypto_kem_dec(ss, c, dk) == 0);
    print_hex("K", ss, sizeof(ss));
  }
  else
  {
    goto usage;
  }

  return 0;

usage:
  fprintf(stderr,
          "Usage:\n"
          "  wycheproof_mlkem{lvl} keygen_seed seed=HEX\n"
          "  wycheproof_mlkem{lvl} encaps ek=HEX m=HEX\n"
          "  wycheproof_mlkem{lvl} decaps dk=HEX c=HEX\n");
  return 1;
}
