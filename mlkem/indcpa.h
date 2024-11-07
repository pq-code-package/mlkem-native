// SPDX-License-Identifier: Apache-2.0
#ifndef INDCPA_H
#define INDCPA_H

#include <stdint.h>
#include "params.h"
#include "polyvec.h"

typedef struct {
  polyvec skpv;
} mlkem_indcpa_secret_key;

typedef struct {
  polyvec at[MLKEM_K]; /* transposed matrix */
  polyvec pkpv;
  uint8_t seed[MLKEM_SYMBYTES];
} mlkem_indcpa_public_key;

#define gen_matrix MLKEM_NAMESPACE(gen_matrix)
void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES], int transposed);

#define indcpa_serialize_pk MLKEM_NAMESPACE(indcpa_serialize_pk)
void indcpa_serialize_pk(uint8_t pks[MLKEM_INDCPA_PUBLICKEYBYTES],
                         const mlkem_indcpa_public_key *pk);
#define indcpa_deserialize_pk MLKEM_NAMESPACE(indcpa_deserialize_pk)
void indcpa_deserialize_pk(mlkem_indcpa_public_key *pk,
                           const uint8_t pks[MLKEM_INDCPA_PUBLICKEYBYTES]);

#define indcpa_serialize_sk MLKEM_NAMESPACE(indcpa_serialize_sk)
void indcpa_serialize_sk(uint8_t sks[MLKEM_INDCPA_SECRETKEYBYTES],
                         const mlkem_indcpa_secret_key *sk);

#define indcpa_deserialize_sk MLKEM_NAMESPACE(indcpa_deserialize_sk)
void indcpa_deserialize_sk(mlkem_indcpa_secret_key *sk,
                           const uint8_t sks[MLKEM_INDCPA_SECRETKEYBYTES]);

#define indcpa_keypair_derand MLKEM_NAMESPACE(indcpa_keypair_derand)
void indcpa_keypair_derand(mlkem_indcpa_public_key *pk,
                           mlkem_indcpa_secret_key *sk,
                           const uint8_t coins[MLKEM_SYMBYTES]);

#define indcpa_enc MLKEM_NAMESPACE(indcpa_enc)
void indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const mlkem_indcpa_public_key *pk,
                const uint8_t coins[MLKEM_SYMBYTES]);

#define indcpa_dec MLKEM_NAMESPACE(indcpa_dec)
void indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t c[MLKEM_INDCPA_BYTES],
                const mlkem_indcpa_secret_key *sk);

#endif
