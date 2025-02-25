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

/* Level namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define mlk_check_pk MLK_ADD_LEVEL(mlk_check_pk)
#define mlk_check_sk MLK_ADD_LEVEL(mlk_check_sk)
#define mlk_check_pct MLK_ADD_LEVEL(mlk_check_pct)
/* End of level namespacing */

#if defined(CBMC)
/* Redeclaration with contract needed for CBMC only */
int memcmp(const void *str1, const void *str2, size_t n)
__contract__(
  requires(memory_no_alias(str1, n))
  requires(memory_no_alias(str2, n))
);
#endif

/*************************************************
 * Name:        mlk_check_pk
 *
 * Description: Implements modulus check mandated by FIPS 203,
 *              i.e., ensures that coefficients are in [0,q-1].
 *
 * Arguments:   - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_INDCCA_PUBLICKEYBYTES
 *                 bytes)
 *
 * Returns: - 0 on success
 *          - -1 on failure
 *
 * Specification: Implements [FIPS 203, Section 7.2, 'modulus check']
 *
 **************************************************/

/* Reference: Not implemented in the reference implementation. */
MLK_MUST_CHECK_RETURN_VALUE
static int mlk_check_pk(const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES])
{
  int res;
  mlk_polyvec p;
  uint8_t p_reencoded[MLKEM_POLYVECBYTES];

  mlk_polyvec_frombytes(p, pk);
  mlk_polyvec_reduce(p);
  mlk_polyvec_tobytes(p_reencoded, p);

  /* We use a constant-time memcmp here to avoid having to
   * declassify the PK before the PCT has succeeded. */
  res = mlk_ct_memcmp(pk, p_reencoded, MLKEM_POLYVECBYTES) ? -1 : 0;

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(p_reencoded, sizeof(p_reencoded));
  mlk_zeroize(&p, sizeof(p));
  return res;
}

/*************************************************
 * Name:        mlk_check_sk
 *
 * Description: Implements public key hash check mandated by FIPS 203,
 *              i.e., ensures that
 *              sk[768𝑘+32 ∶ 768𝑘+64] = H(pk)= H(sk[384𝑘 : 768𝑘+32])
 *
 * Arguments:   - const uint8_t *sk: pointer to input private key
 *                (an already allocated array of MLKEM_INDCCA_SECRETKEYBYTES
 *                 bytes)
 *
 * Returns: - 0 on success
 *          - -1 on failure
 *
 * Specification: Implements [FIPS 203, Section 7.3, 'hash check']
 *
 **************************************************/

/* Reference: Not implemented in the reference implementation. */
MLK_MUST_CHECK_RETURN_VALUE
static int mlk_check_sk(const uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES])
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

  mlk_hash_h(test, sk + MLKEM_INDCPA_SECRETKEYBYTES,
             MLKEM_INDCCA_PUBLICKEYBYTES);
  res = memcmp(sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, test,
               MLKEM_SYMBYTES)
            ? -1
            : 0;

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(test, sizeof(test));
  return res;
}

MLK_MUST_CHECK_RETURN_VALUE
static int mlk_check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                         uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES])
__contract__(
  requires(memory_no_alias(pk, MLKEM_INDCCA_PUBLICKEYBYTES))
  requires(memory_no_alias(sk, MLKEM_INDCCA_SECRETKEYBYTES)));

#if defined(MLK_KEYGEN_PCT)
/* Specification:
 * Partially implements 'Pairwise Consistency Test' [FIPS 140-3 IG] and
 * [FIPS 203, Section 7.1, Pairwise Consistency]. */

/* Reference: Not implemented in the reference implementation. */
static int mlk_check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                         uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  int res;
  uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES];
  uint8_t ss_enc[MLKEM_SSBYTES], ss_dec[MLKEM_SSBYTES];

  res = crypto_kem_enc(ct, ss_enc, pk);
  if (res != 0)
  {
    goto cleanup;
  }

  res = crypto_kem_dec(ss_dec, ct, sk);
  if (res != 0)
  {
    goto cleanup;
  }

#if defined(MLK_KEYGEN_PCT_BREAKAGE_TEST)
  /* Deliberately break PCT for testing purposes */
  if (mlk_break_pct())
  {
    ss_enc[0] = ~ss_enc[0];
  }
#endif /* MLK_KEYGEN_PCT_BREAKAGE_TEST */

  res = mlk_ct_memcmp(ss_enc, ss_dec, sizeof(ss_dec));

cleanup:
  /* The result of the PCT is public. */
  MLK_CT_TESTING_DECLASSIFY(&res, sizeof(res));

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(ct, sizeof(ct));
  mlk_zeroize(ss_enc, sizeof(ss_enc));
  mlk_zeroize(ss_dec, sizeof(ss_dec));
  return res;
}
#else  /* !MLKEM_KEYGEN_PCT */
static int mlk_check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                         uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  /* Skip PCT */
  ((void)pk);
  ((void)sk);
  return 0;
}
#endif /* MLKEM_KEYGEN_PCT */


MLK_EXTERNAL_API
void crypto_kem_marshal_pk(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                           const mlk_public_key *pks)
{
  const mlk_public_key_internal *pki = (mlk_public_key_internal *)pks;
  mlk_indcpa_marshal_pk(pk, &pki->indcpa_pk);
}

MLK_EXTERNAL_API
int crypto_kem_parse_pk(mlk_public_key *pks,
                        const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES])
{
  mlk_public_key_internal *pki = (mlk_public_key_internal *)pks;
  if (mlk_check_pk(pk))
  {
    return -1;
  }
  mlk_indcpa_parse_pk(&pki->indcpa_pk, pk);
  mlk_hash_h(pki->hpk, pk, MLKEM_INDCCA_PUBLICKEYBYTES);
  return 0;
}

MLK_EXTERNAL_API
void crypto_kem_marshal_sk(uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                           const mlk_secret_key *sks)
{
  mlk_secret_key_internal *ski = (mlk_secret_key_internal *)sks;
  mlk_indcpa_marshal_sk(sk, &ski->indcpa_sk);
  mlk_indcpa_marshal_pk(sk + MLKEM_INDCPA_SECRETKEYBYTES, &ski->indcpa_pk);
  memcpy(sk + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES,
         ski->hpk, MLKEM_SYMBYTES);
  memcpy(sk + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES +
             MLKEM_SYMBYTES,
         ski->z, MLKEM_SYMBYTES);
}

MLK_EXTERNAL_API
int crypto_kem_parse_sk(mlk_secret_key *sks,
                        const uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  mlk_secret_key_internal *ski = (mlk_secret_key_internal *)sks;
  if (mlk_check_sk(sk))
  {
    return -1;
  }
  mlk_indcpa_parse_sk(&ski->indcpa_sk, sk);
  mlk_indcpa_parse_pk(&ski->indcpa_pk, sk + MLKEM_INDCPA_SECRETKEYBYTES);
  memcpy(ski->hpk,
         sk + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES,
         MLKEM_SYMBYTES);
  memcpy(ski->z,
         sk + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES +
             MLKEM_SYMBYTES,
         MLKEM_SYMBYTES);
  return 0;
}


MLK_EXTERNAL_API
int crypto_kem_keypair_derand_struct(mlk_public_key *pk, mlk_secret_key *sk,
                                     const uint8_t coins[2 * MLKEM_SYMBYTES])
{
  mlk_public_key_internal *pki = (mlk_public_key_internal *)pk;
  mlk_secret_key_internal *ski = (mlk_secret_key_internal *)sk;
  MLK_ALIGN uint8_t pks[MLKEM_INDCCA_PUBLICKEYBYTES];

  mlk_indcpa_keypair_derand(&ski->indcpa_pk, &ski->indcpa_sk, coins);

  /* pre-compute H(pk) */
  mlk_indcpa_marshal_pk(pks, &ski->indcpa_pk);
  mlk_hash_h(ski->hpk, pks, MLKEM_INDCCA_PUBLICKEYBYTES);

  /*
   * copy over indcpa pk and H(pk) to public key
   * pk is NULL during parsing before decaps as the pk is not needed
   **/
  if (pk != NULL)
  {
    memcpy(&pki->indcpa_pk, &ski->indcpa_pk, sizeof(mlk_indcpa_public_key));
    memcpy(pki->hpk, ski->hpk, MLKEM_SYMBYTES);
  }

  /* Value z for pseudo-random output on reject */
  memcpy(ski->z, coins + MLKEM_SYMBYTES, MLKEM_SYMBYTES);

  /* Declassify public key */
  MLK_CT_TESTING_DECLASSIFY(&pki->indcpa_pk, sizeof(mlk_indcpa_public_key));


  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(pks, sizeof(pks));
  return 0;
}

MLK_EXTERNAL_API
int crypto_kem_keypair_struct(mlk_public_key *pk, mlk_secret_key *sk)
{
  int res;
  MLK_ALIGN uint8_t coins[2 * MLKEM_SYMBYTES];

  /* Acquire necessary randomness, and mark it as secret. */
  randombytes(coins, 2 * MLKEM_SYMBYTES);
  MLK_CT_TESTING_SECRET(coins, sizeof(coins));

  res = crypto_kem_keypair_derand_struct(pk, sk, coins);


  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(coins, sizeof(coins));
  return res;
}


/* Reference: `crypto_kem_keypair_derand()` in the reference implementation
 *            - We optionally include PCT which is not present in
 *              the reference code. */
MLK_EXTERNAL_API
int crypto_kem_keypair_derand(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                              uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                              const uint8_t coins[2 * MLKEM_SYMBYTES])
{
  int res;
  mlk_public_key pks;
  mlk_secret_key sks;


  res = crypto_kem_keypair_derand_struct(&pks, &sks, coins);


  crypto_kem_marshal_pk(pk, &pks);
  crypto_kem_marshal_sk(sk, &sks);

  /* Pairwise Consistency Test (PCT) (FIPS 140-3 IPG) */
  if (mlk_check_pct(pk, sk))
  {
    return -1;
  }

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(&pks, sizeof(mlk_public_key));
  mlk_zeroize(&sks, sizeof(mlk_secret_key));
  return res;
}

/* Reference: `crypto_kem_keypair()` in the reference implementation
 *            - We zeroize the stack buffer */
MLK_EXTERNAL_API
int crypto_kem_keypair(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                       uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  int res;
  MLK_ALIGN uint8_t coins[2 * MLKEM_SYMBYTES];

  /* Acquire necessary randomness, and mark it as secret. */
  mlk_randombytes(coins, 2 * MLKEM_SYMBYTES);
  MLK_CT_TESTING_SECRET(coins, sizeof(coins));

  res = crypto_kem_keypair_derand(pk, sk, coins);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(coins, sizeof(coins));
  return res;
}

MLK_EXTERNAL_API
int crypto_kem_enc_derand_struct(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                                 uint8_t ss[MLKEM_SSBYTES],
                                 const mlk_public_key *pk,
                                 const uint8_t coins[MLKEM_SYMBYTES])
{
  const mlk_public_key_internal *pki = (mlk_public_key_internal *)pk;
  MLK_ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  /* Will contain key, coins */
  MLK_ALIGN uint8_t kr[2 * MLKEM_SYMBYTES];

  memcpy(buf, coins, MLKEM_SYMBYTES);

  /* Multitarget countermeasure for coins + contributory KEM */
  memcpy(buf + MLKEM_SYMBYTES, pki->hpk, MLKEM_SYMBYTES);
  mlk_hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* coins are in kr+MLKEM_SYMBYTES */
  mlk_indcpa_enc(ct, buf, &pki->indcpa_pk, kr + MLKEM_SYMBYTES);

  memcpy(ss, kr, MLKEM_SYMBYTES);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(buf, sizeof(buf));
  mlk_zeroize(kr, sizeof(kr));
  return 0;
}

MLK_EXTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int crypto_kem_enc_struct(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                          uint8_t ss[MLKEM_SSBYTES], const mlk_public_key *pk)
{
  int res;
  MLK_ALIGN uint8_t coins[MLKEM_SYMBYTES];

  randombytes(coins, MLKEM_SYMBYTES);
  MLK_CT_TESTING_SECRET(coins, sizeof(coins));

  res = crypto_kem_enc_derand_struct(ct, ss, pk, coins);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(coins, sizeof(coins));
  return res;
}

/* Reference: `crypto_kem_enc_derand()` in the reference implementation
 *            - We include public key check
 *            - We include stack buffer zeroization */
MLK_EXTERNAL_API
int crypto_kem_enc_derand(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                          uint8_t ss[MLKEM_SSBYTES],
                          const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                          const uint8_t coins[MLKEM_SYMBYTES])
{
  int res;
  mlk_public_key pks;
  if (crypto_kem_parse_pk(&pks, pk))
  {
    return -1;
  }

  res = crypto_kem_enc_derand_struct(ct, ss, &pks, coins);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(&pks, sizeof(mlk_public_key));
  return res;
}



/* Reference: `crypto_kem_enc()` in the reference implementation
 *            - We include stack buffer zeroization */
MLK_EXTERNAL_API
int crypto_kem_enc(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                   uint8_t ss[MLKEM_SSBYTES],
                   const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES])
{
  int res;
  MLK_ALIGN uint8_t coins[MLKEM_SYMBYTES];

  mlk_randombytes(coins, MLKEM_SYMBYTES);
  MLK_CT_TESTING_SECRET(coins, sizeof(coins));

  res = crypto_kem_enc_derand(ct, ss, pk, coins);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(coins, sizeof(coins));
  return res;
}



MLK_EXTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int crypto_kem_dec_struct(uint8_t ss[MLKEM_SSBYTES],
                          const uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                          const mlk_secret_key *sk)
{
  const mlk_secret_key_internal *ski = (mlk_secret_key_internal *)sk;
  uint8_t fail;
  MLK_ALIGN uint8_t buf[2 * MLKEM_SYMBYTES];
  /* Will contain key, coins */
  MLK_ALIGN uint8_t kr[2 * MLKEM_SYMBYTES];
  MLK_ALIGN uint8_t tmp[MLKEM_SYMBYTES + MLKEM_INDCCA_CIPHERTEXTBYTES];

  mlk_indcpa_dec(buf, ct, &ski->indcpa_sk);

  /* Multitarget countermeasure for coins + contributory KEM */
  memcpy(buf + MLKEM_SYMBYTES, ski->hpk, MLKEM_SYMBYTES);
  mlk_hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* Recompute and compare ciphertext */
  /* coins are in kr+MLKEM_SYMBYTES */
  mlk_indcpa_enc(tmp, buf, &ski->indcpa_pk, kr + MLKEM_SYMBYTES);
  fail = mlk_ct_memcmp(ct, tmp, MLKEM_INDCCA_CIPHERTEXTBYTES);

  /* Compute rejection key */
  memcpy(tmp, ski->z, MLKEM_SYMBYTES);
  memcpy(tmp + MLKEM_SYMBYTES, ct, MLKEM_INDCCA_CIPHERTEXTBYTES);
  mlk_hash_j(ss, tmp, sizeof(tmp));

  /* Copy true key to return buffer if fail is 0 */
  mlk_ct_cmov_zero(ss, kr, MLKEM_SYMBYTES, fail);

  /* Specification: Partially implements
   * [FIPS 203, Section 3.3, Destruction of intermediate values] */
  mlk_zeroize(buf, sizeof(buf));
  mlk_zeroize(kr, sizeof(kr));
  mlk_zeroize(tmp, sizeof(tmp));
  return 0;
}

/* Reference: `crypto_kem_dec()` in the reference implementation
 *            - We include secret key check
 *            - We include stack buffer zeroization */
MLK_EXTERNAL_API
int crypto_kem_dec(uint8_t ss[MLKEM_SSBYTES],
                   const uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                   const uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES])
{
  int res;
  mlk_secret_key sks;

  if (crypto_kem_parse_sk(&sks, sk))
  {
    return -1;
  }

  res = crypto_kem_dec_struct(ss, ct, &sks);
  mlk_zeroize(&sks, sizeof(mlk_secret_key));
  return res;
}

MLK_EXTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int crypto_kem_sk_from_seed(mlk_secret_key *sk,
                            const uint8_t coins[2 * MLKEM_SYMBYTES])
{
  return crypto_kem_keypair_derand_struct(NULL, sk, coins);
}

MLK_EXTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int crypto_kem_pk_from_sk(mlk_public_key *pk, mlk_secret_key *sk)
{
  mlk_public_key_internal *pki = (mlk_public_key_internal *)pk;
  mlk_secret_key_internal *ski = (mlk_secret_key_internal *)sk;
  memcpy(pki->hpk, ski->hpk, MLKEM_SYMBYTES);
  memcpy(&pki->indcpa_pk, &ski->indcpa_pk, sizeof(mlk_indcpa_public_key));
  return 0;
}



/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef mlk_check_pk
#undef mlk_check_sk
#undef mlk_check_pct
