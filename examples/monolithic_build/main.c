/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#define MLKEM_NATIVE_CONFIG_FILE "config_a.h"
#include "mlkem_native_all.c"
#undef MLKEM_NATIVE_CONFIG_FILE

#define MLKEM_NATIVE_CONFIG_FILE "config_b.h"
#include "mlkem_native_all.c"
#undef MLKEM_NATIVE_CONFIG_FILE

/* Some scheme parameters from META.json
 *
 * TODO: One should be able to get those more easily,
 * but after mlkem_native_all.c the MLKEM_XXX macros
 * have already been undefined.
 * This should be sorted by providing a new api.h
 * header that can be included and relies solely on
 * the config.h; the present kem.h does not yet have
 * this property. */
#define MLKEM768_SECRETKEYBYTES 2400
#define MLKEM768_PUBLICKEYBYTES 1184
#define MLKEM768_CIPHERTEXTBYTES 1088
#define MLKEM768_BYTES 32

#define MLKEM1024_SECRETKEYBYTES 3168
#define MLKEM1024_PUBLICKEYBYTES 1568
#define MLKEM1024_CIPHERTEXTBYTES 1568
#define MLKEM1024_BYTES 32

/* Public API declaration -- those, too, should not be done
 * manually, but come from a config-dependent api.h. */
int mlkem768_keypair(uint8_t *pk, uint8_t *sk);
int mlkem768_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk);
int mlkem768_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);

int mlkem1024_keypair(uint8_t *pk, uint8_t *sk);
int mlkem1024_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk);
int mlkem1024_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);

static int test_keys_mlkem768(void)
{
  uint8_t pk[MLKEM768_PUBLICKEYBYTES];
  uint8_t sk[MLKEM768_SECRETKEYBYTES];
  uint8_t ct[MLKEM768_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM768_BYTES];
  uint8_t key_b[MLKEM768_BYTES];

  /* Alice generates a public key */
  mlkem768_keypair(pk, sk);

  /* Bob derives a secret key and creates a response */
  mlkem768_enc(ct, key_b, pk);

  /* Alice uses Bobs response to get her shared key */
  mlkem768_dec(key_a, ct, sk);

  if (memcmp(key_a, key_b, MLKEM768_BYTES))
  {
    printf("[MLKEM-768] ERROR keys\n");
    return 1;
  }

  return 0;
}

static int test_keys_mlkem1024(void)
{
  uint8_t pk[MLKEM1024_PUBLICKEYBYTES];
  uint8_t sk[MLKEM1024_SECRETKEYBYTES];
  uint8_t ct[MLKEM1024_CIPHERTEXTBYTES];
  uint8_t key_a[MLKEM1024_BYTES];
  uint8_t key_b[MLKEM1024_BYTES];

  /* Alice generates a public key */
  mlkem1024_keypair(pk, sk);

  /* Bob derives a secret key and creates a response */
  mlkem1024_enc(ct, key_b, pk);

  /* Alice uses Bobs response to get her shared key */
  mlkem1024_dec(key_a, ct, sk);

  if (memcmp(key_a, key_b, MLKEM1024_BYTES))
  {
    printf("[MLKEM-1024] ERROR keys\n");
    return 1;
  }

  return 0;
}

int main(void)
{
  if (test_keys_mlkem768() != 0)
  {
    return 1;
  }

  if (test_keys_mlkem1024() != 0)
  {
    return 1;
  }

  return 0;
}
