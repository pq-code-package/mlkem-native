// SPDX-License-Identifier: Apache-2.0
#include "kem.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "params.h"
#include "randombytes.h"
#include "symmetric.h"
#include "verify.h"

/*************************************************
 * Name:        check_pk
 *
 * Description: Implements modulus check mandated by FIPS203,
 *              i.e., ensures that coefficients are in [0,q-1].
 *              Described in Section 7.2 of FIPS203.
 *
 * Arguments:   - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 **
 * Returns 0 on success, and -1 on failure
 **************************************************/
static int check_pk(const uint8_t pk[MLKEM_PUBLICKEYBYTES]) {
  polyvec p;
  uint8_t p_reencoded[MLKEM_POLYVECBYTES];
  polyvec_frombytes(&p, pk);
  polyvec_reduce(&p);
  polyvec_tobytes(p_reencoded, &p);
  // Data is public, so a variable-time memcmp() is OK
  if (memcmp(pk, p_reencoded, MLKEM_POLYVECBYTES)) {
    return -1;
  }
  return 0;
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
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *
 * Returns 0 on success, and -1 on failure
 **************************************************/
static int check_sk(const uint8_t sk[MLKEM_SECRETKEYBYTES]) {
  uint8_t test[MLKEM_SYMBYTES];
  // The parts of `sk` being hashed and compared here are public, so
  // no public information is leaked through the runtime or the return value
  // of this function.
  hash_h(test, sk + MLKEM_INDCPA_SECRETKEYBYTES, MLKEM_PUBLICKEYBYTES);
  if (memcmp(sk + MLKEM_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, test,
             MLKEM_SYMBYTES)) {
    return -1;
  }
  return 0;
}


int crypto_kem_serialize_sk(uint8_t sks[MLKEM_SECRETKEYBYTES],
                            const mlkem_secret_key *sk) {
  indcpa_serialize_sk(sks, &sk->indcpa_sk);
  indcpa_serialize_pk(sks + MLKEM_INDCPA_SECRETKEYBYTES, &sk->indcpa_pk);
  memcpy(sks + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES,
         sk->hpk, MLKEM_SYMBYTES);
  memcpy(sks + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES +
             MLKEM_SYMBYTES,
         sk->z, MLKEM_SYMBYTES);
  return 0;
}

int crypto_kem_deserialize_sk(mlkem_secret_key *sk,
                              const uint8_t sks[MLKEM_SECRETKEYBYTES]) {
  if (check_sk(sks)) {
    return -1;
  }
  indcpa_deserialize_sk(&sk->indcpa_sk, sks);
  indcpa_deserialize_pk(&sk->indcpa_pk, sks + MLKEM_INDCPA_SECRETKEYBYTES);
  memcpy(sk->hpk,
         sks + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES,
         MLKEM_SYMBYTES);
  memcpy(sk->z,
         sks + MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES +
             MLKEM_SYMBYTES,
         MLKEM_SYMBYTES);

  return 0;
}

int crypto_kem_serialize_pk(uint8_t pks[MLKEM_PUBLICKEYBYTES],
                            const mlkem_public_key *pk) {
  indcpa_serialize_pk(pks, &pk->indcpa_pk);
  return 0;
}

int crypto_kem_deserialize_pk(mlkem_public_key *pk,
                              const uint8_t pks[MLKEM_PUBLICKEYBYTES]) {
  if (check_pk(pks)) {
    return -1;
  }
  indcpa_deserialize_pk(&pk->indcpa_pk, pks);
  hash_h(pk->hpk, pks, MLKEM_PUBLICKEYBYTES);
  return 0;
}


/*************************************************
 * Name:        crypto_kem_keypair_derand
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t *pk: pointer to output public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *              - uint8_t *sk: pointer to output private key
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *              - uint8_t *coins: pointer to input randomness
 *                (an already allocated array filled with 2*MLKEM_SYMBYTES
 *random bytes)
 **
 * Returns 0 (success)
 **************************************************/
int crypto_kem_keypair_derand(mlkem_public_key *pk, mlkem_secret_key *sk,
                              const uint8_t *coins) {
  indcpa_keypair_derand(&sk->indcpa_pk, &sk->indcpa_sk, coins);

  // pre-compute H(pk)
  uint8_t pks[MLKEM_PUBLICKEYBYTES];
  indcpa_serialize_pk(pks, &sk->indcpa_pk);
  hash_h(sk->hpk, pks, MLKEM_PUBLICKEYBYTES);


  // copy over indcpa pk and H(pk) to public key
  // pk is NULL during deseralization before decaps as the pk is not needed
  if (pk != NULL) {
    memcpy(&pk->indcpa_pk, &sk->indcpa_pk, sizeof(mlkem_indcpa_public_key));
    memcpy(pk->hpk, sk->hpk, MLKEM_SYMBYTES);
  }

  // Value z for pseudo-random output on reject
  memcpy(sk->z, coins + MLKEM_SYMBYTES, MLKEM_SYMBYTES);

  // seed to regenerate whole secret key
  memcpy(sk->seed, coins, MLKEM_SYMBYTES);
  return 0;
}

/*************************************************
 * Name:        crypto_kem_keypair
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t *pk: pointer to output public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *              - uint8_t *sk: pointer to output private key
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *
 * Returns 0 (success)
 **************************************************/
int crypto_kem_keypair(mlkem_public_key *pk, mlkem_secret_key *sk) {
  uint8_t coins[2 * MLKEM_SYMBYTES] ALIGN;
  randombytes(coins, 2 * MLKEM_SYMBYTES);
  crypto_kem_keypair_derand(pk, sk, coins);
  return 0;
}

/*************************************************
 * Name:        crypto_kem_enc_derand
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text
 *                (an already allocated array of MLKEM_CIPHERTEXTBYTES bytes)
 *              - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *              - const uint8_t *coins: pointer to input randomness
 *                (an already allocated array filled with MLKEM_SYMBYTES random
 *bytes)
 **
 * Returns 0 (success)
 **************************************************/
int crypto_kem_enc_derand(uint8_t ct[MLKEM_CIPHERTEXTBYTES],
                          uint8_t ss[MLKEM_SSBYTES], const mlkem_public_key *pk,
                          const uint8_t *coins) {
  uint8_t buf[2 * MLKEM_SYMBYTES] ALIGN;
  /* Will contain key, coins */
  uint8_t kr[2 * MLKEM_SYMBYTES] ALIGN;

  memcpy(buf, coins, MLKEM_SYMBYTES);

  /* Multitarget countermeasure for coins + contributory KEM */
  memcpy(buf + MLKEM_SYMBYTES, pk->hpk, MLKEM_SYMBYTES);
  hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* coins are in kr+MLKEM_SYMBYTES */
  indcpa_enc(ct, buf, &pk->indcpa_pk, kr + MLKEM_SYMBYTES);

  memcpy(ss, kr, MLKEM_SYMBYTES);
  return 0;
}

/*************************************************
 * Name:        crypto_kem_enc
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text
 *                (an already allocated array of MLKEM_CIPHERTEXTBYTES bytes)
 *              - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *pk: pointer to input public key
 *                (an already allocated array of MLKEM_PUBLICKEYBYTES bytes)
 *
 * Returns 0 (success)
 **************************************************/
int crypto_kem_enc(uint8_t ct[MLKEM_CIPHERTEXTBYTES], uint8_t ss[MLKEM_SSBYTES],
                   const mlkem_public_key *pk) {
  uint8_t coins[MLKEM_SYMBYTES] ALIGN;
  randombytes(coins, MLKEM_SYMBYTES);
  return crypto_kem_enc_derand(ct, ss, pk, coins);
}

/*************************************************
 * Name:        crypto_kem_dec
 *
 * Description: Generates shared secret for given
 *              cipher text and private key
 *
 * Arguments:   - uint8_t *ss: pointer to output shared secret
 *                (an already allocated array of MLKEM_SSBYTES bytes)
 *              - const uint8_t *ct: pointer to input cipher text
 *                (an already allocated array of MLKEM_CIPHERTEXTBYTES bytes)
 *              - const uint8_t *sk: pointer to input private key
 *                (an already allocated array of MLKEM_SECRETKEYBYTES bytes)
 *
 * Returns 0 (success)
 *
 * On failure, ss will contain a pseudo-random value.
 **************************************************/
int crypto_kem_dec(uint8_t ss[MLKEM_SSBYTES],
                   const uint8_t ct[MLKEM_CIPHERTEXTBYTES],
                   const mlkem_secret_key *sk) {
  int fail;
  uint8_t buf[2 * MLKEM_SYMBYTES] ALIGN;
  /* Will contain key, coins */
  uint8_t kr[2 * MLKEM_SYMBYTES] ALIGN;
  uint8_t cmp[MLKEM_CIPHERTEXTBYTES + MLKEM_SYMBYTES] ALIGN;

  indcpa_dec(buf, ct, &sk->indcpa_sk);

  /* Multitarget countermeasure for coins + contributory KEM */
  memcpy(buf + MLKEM_SYMBYTES, sk->hpk, MLKEM_SYMBYTES);
  hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* coins are in kr+MLKEM_SYMBYTES */
  indcpa_enc(cmp, buf, &sk->indcpa_pk, kr + MLKEM_SYMBYTES);

  fail = verify(ct, cmp, MLKEM_CIPHERTEXTBYTES);

  /* Compute rejection key */
  rkprf(ss, sk->z, ct);

  /* Copy true key to return buffer if fail is false */
  cmov(ss, kr, MLKEM_SYMBYTES, !fail);

  return 0;
}
