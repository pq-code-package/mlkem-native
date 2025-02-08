/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "indcpa.h"
#include "kem.h"
#include "randombytes.h"
#include "symmetric.h"
#include "verify.h"

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define check_pk MLK_NAMESPACE_K(check_pk)
#define check_sk MLK_NAMESPACE_K(check_sk)
/* End of static namespacing */

#if defined(CBMC)
/* Redeclaration with contract needed for CBMC only */
int memcmp(const void *str1, const void *str2, size_t n)
__contract__(
  requires(memory_no_alias(str1, n))
  requires(memory_no_alias(str2, n))
);
#endif

/*************************************************
 * Name:        check_pk
 *
 * Description: Implements modulus check mandated by FIPS203,
 *              i.e., ensures that coefficients are in [0,q-1].
 *              Described in Section 7.2 of FIPS203.
 *
 * Arguments:   - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_INDCCA_PUBLICKEYBYTES
 *                 bytes)
 *
 * Returns 0 on success, and -1 on failure
 **************************************************/
static int check_pk(const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES])
{
  int res;
  polyvec p;
  uint8_t p_reencoded[MLKEM_POLYVECBYTES];

  polyvec_frombytes(&p, pk);
  polyvec_reduce(&p);
  polyvec_tobytes(p_reencoded, &p);

  /* Data is public, so a variable-time memcmp() is OK */
  res = memcmp(pk, p_reencoded, MLKEM_POLYVECBYTES) ? -1 : 0;

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(p_reencoded, sizeof(p_reencoded));
  ct_zeroize(&p, sizeof(p));
  return res;
}

/*************************************************
 * Name:        check_sk
 *
 * Description: Implements public key hash check mandated by FIPS203,
 *              i.e., ensures that
 *              sk[768𝑘+32 ∶ 768𝑘+64] = H(pk)= H(sk[384𝑘 : 768𝑘+32])
 *              Described in Section 7.3 of FIPS203.
 *
 * Arguments:   - const uint8_t *sk: pointer to input private key
 *                (an already allocated array of MLKEM_INDCCA_SECRETKEYBYTES
 *                 bytes)
 *
 * Returns 0 on success, and -1 on failure
 **************************************************/
static int check_sk(const uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  int res;
  MLK_ALIGN uint8_t test[MLKEM_SYMBYTES];
  /*
   * The parts of `sk` being hashed and compared here are public, so
   * no public information is leaked through the runtime or the return value
   * of this function.
   */

  /* Declassify the public part of the secret key */
  MLK_CT_TESTING_DECLASSIFY(sk + MLKEM_INDCPA_SECRETKEYBYTES,
                            MLKEM_INDCCA_PUBLICKEYBYTES);
  MLK_CT_TESTING_DECLASSIFY(
      sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, MLKEM_SYMBYTES);

  hash_h(test, sk + MLKEM_INDCPA_SECRETKEYBYTES, MLKEM_INDCCA_PUBLICKEYBYTES);
  res = memcmp(sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, test,
               MLKEM_SYMBYTES)
            ? -1
            : 0;

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(test, sizeof(test));
  return res;
}

int crypto_kem_keypair_derand(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                              uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                              const uint8_t *coins)
{
  indcpa_keypair_derand(pk, sk, coins);
  memcpy(sk + MLKEM_INDCPA_SECRETKEYBYTES, pk, MLKEM_INDCCA_PUBLICKEYBYTES);
  hash_h(sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, pk,
         MLKEM_INDCCA_PUBLICKEYBYTES);
  /* Value z for pseudo-random output on reject */
  memcpy(sk + MLKEM_INDCCA_SECRETKEYBYTES - MLKEM_SYMBYTES,
         coins + MLKEM_SYMBYTES, MLKEM_SYMBYTES);
  return 0;
}

int crypto_kem_keypair(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                       uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  MLK_ALIGN uint8_t coins[2 * MLKEM_SYMBYTES];
  randombytes(coins, 2 * MLKEM_SYMBYTES);
  crypto_kem_keypair_derand(pk, sk, coins);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(coins, sizeof(coins));

  return 0;
}

int crypto_kem_enc_derand(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                          uint8_t ss[MLKEM_SSBYTES],
                          const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                          const uint8_t coins[MLKEM_SYMBYTES])
{
  MLK_ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  /* Will contain key, coins */
  MLK_ALIGN uint8_t kr[2 * MLKEM_SYMBYTES];

  if (check_pk(pk))
  {
    return -1;
  }

  memcpy(buf, coins, MLKEM_SYMBYTES);

  /* Multitarget countermeasure for coins + contributory KEM */
  hash_h(buf + MLKEM_SYMBYTES, pk, MLKEM_INDCCA_PUBLICKEYBYTES);
  hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* coins are in kr+MLKEM_SYMBYTES */
  indcpa_enc(ct, buf, pk, kr + MLKEM_SYMBYTES);

  memcpy(ss, kr, MLKEM_SYMBYTES);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(buf, sizeof(buf));
  ct_zeroize(kr, sizeof(kr));

  return 0;
}

int crypto_kem_enc(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                   uint8_t ss[MLKEM_SSBYTES],
                   const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES])
{
  int res;
  MLK_ALIGN uint8_t coins[MLKEM_SYMBYTES];
  randombytes(coins, MLKEM_SYMBYTES);
  res = crypto_kem_enc_derand(ct, ss, pk, coins);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(coins, sizeof(coins));
  return res;
}

int crypto_kem_dec(uint8_t ss[MLKEM_SSBYTES],
                   const uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                   const uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  uint8_t fail;
  MLK_ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  /* Will contain key, coins */
  MLK_ALIGN uint8_t kr[2 * MLKEM_SYMBYTES];
  MLK_ALIGN uint8_t tmp[MLKEM_SYMBYTES + MLKEM_INDCCA_CIPHERTEXTBYTES];

  const uint8_t *pk = sk + MLKEM_INDCPA_SECRETKEYBYTES;

  if (check_sk(sk))
  {
    return -1;
  }

  indcpa_dec(buf, ct, sk);

  /* Multitarget countermeasure for coins + contributory KEM */
  memcpy(buf + MLKEM_SYMBYTES,
         sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, MLKEM_SYMBYTES);
  hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* Recompute and compare ciphertext */
  /* coins are in kr+MLKEM_SYMBYTES */
  indcpa_enc(tmp, buf, pk, kr + MLKEM_SYMBYTES);
  fail = ct_memcmp(ct, tmp, MLKEM_INDCCA_CIPHERTEXTBYTES);

  /* Compute rejection key */
  memcpy(tmp, sk + MLKEM_INDCCA_SECRETKEYBYTES - MLKEM_SYMBYTES,
         MLKEM_SYMBYTES);
  memcpy(tmp + MLKEM_SYMBYTES, ct, MLKEM_INDCCA_CIPHERTEXTBYTES);
  hash_j(ss, tmp, sizeof(tmp));

  /* Copy true key to return buffer if fail is 0 */
  ct_cmov_zero(ss, kr, MLKEM_SYMBYTES, fail);

  /* FIPS 203. Section 3.3 Destruction of intermediate values. */
  ct_zeroize(buf, sizeof(buf));
  ct_zeroize(kr, sizeof(kr));
  ct_zeroize(tmp, sizeof(tmp));

  return 0;
}

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef check_pk
#undef check_sk
