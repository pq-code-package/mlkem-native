// SPDX-License-Identifier: Apache-2.0
#ifndef KEM_H
#define KEM_H

#include <stdint.h>
#include "indcpa.h"
#include "params.h"

#define CRYPTO_SECRETKEYBYTES MLKEM_SECRETKEYBYTES
#define CRYPTO_PUBLICKEYBYTES MLKEM_PUBLICKEYBYTES
#define CRYPTO_CIPHERTEXTBYTES MLKEM_CIPHERTEXTBYTES
#define CRYPTO_BYTES MLKEM_SSBYTES

#if (MLKEM_K == 2)
#define CRYPTO_ALGNAME "Kyber512"
#elif (MLKEM_K == 3)
#define CRYPTO_ALGNAME "Kyber768"
#elif (MLKEM_K == 4)
#define CRYPTO_ALGNAME "Kyber1024"
#endif


typedef struct {
  mlkem_indcpa_secret_key indcpa_sk;
  mlkem_indcpa_public_key indcpa_pk;
  uint8_t seed[MLKEM_SYMBYTES];
  uint8_t z[MLKEM_SYMBYTES];
  uint8_t hpk[MLKEM_SYMBYTES];
} mlkem_secret_key;


typedef struct {
  mlkem_indcpa_public_key indcpa_pk;
  uint8_t hpk[MLKEM_SYMBYTES];
} mlkem_public_key;

#define crypto_kem_serialize_sk MLKEM_NAMESPACE(serialize_sk)
int crypto_kem_serialize_sk(uint8_t sks[MLKEM_SECRETKEYBYTES],
                            const mlkem_secret_key *sk);
#define crypto_kem_deserialize_sk MLKEM_NAMESPACE(deserialize_sk)
int crypto_kem_deserialize_sk(mlkem_secret_key *sk,
                              const uint8_t sks[MLKEM_SECRETKEYBYTES]);

#define crypto_kem_serialize_pk MLKEM_NAMESPACE(serialize_pk)
int crypto_kem_serialize_pk(uint8_t pks[MLKEM_PUBLICKEYBYTES],
                            const mlkem_public_key *pk);
#define crypto_kem_deserialize_pk MLKEM_NAMESPACE(deserialize_pk)
int crypto_kem_deserialize_pk(mlkem_public_key *pk,
                              const uint8_t pks[MLKEM_PUBLICKEYBYTES]);

#define crypto_kem_keypair_derand MLKEM_NAMESPACE(keypair_derand)
int crypto_kem_keypair_derand(mlkem_public_key *pk, mlkem_secret_key *sk,
                              const uint8_t *coins);
#define crypto_kem_keypair MLKEM_NAMESPACE(keypair)
int crypto_kem_keypair(mlkem_public_key *pk, mlkem_secret_key *sk);

#define crypto_kem_enc_derand MLKEM_NAMESPACE(enc_derand)
int crypto_kem_enc_derand(uint8_t ct[MLKEM_CIPHERTEXTBYTES],
                          uint8_t ss[MLKEM_SSBYTES], const mlkem_public_key *pk,
                          const uint8_t *coins);
#define crypto_kem_enc MLKEM_NAMESPACE(enc)
int crypto_kem_enc(uint8_t ct[MLKEM_CIPHERTEXTBYTES], uint8_t ss[MLKEM_SSBYTES],
                   const mlkem_public_key *pk);
#define crypto_kem_dec MLKEM_NAMESPACE(dec)
int crypto_kem_dec(uint8_t ss[MLKEM_SSBYTES],
                   const uint8_t ct[MLKEM_CIPHERTEXTBYTES],
                   const mlkem_secret_key *sk);

#endif
