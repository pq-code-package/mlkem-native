// SPDX-License-Identifier: Apache-2.0
#ifndef INDCPA_H
#define INDCPA_H

#include <stdint.h>
#include "cbmc.h"
#include "params.h"
#include "polyvec.h"

// clang-format off
#define gen_matrix MLKEM_NAMESPACE(gen_matrix)
void gen_matrix(polyvec *a, const uint8_t seed[MLKEM_SYMBYTES], int transposed)
REQUIRES(IS_FRESH(a, sizeof(polyvec) * MLKEM_K))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
REQUIRES(transposed == 0 || transposed == 1)
ASSIGNS(OBJECT_WHOLE(a))
ENSURES(FORALL(int, x, 0, MLKEM_K - 1, FORALL(int, y, 0, MLKEM_K - 1,
  ARRAY_IN_BOUNDS(int, i, 0, MLKEM_N - 1, a[x].vec[y].coeffs, 0, (MLKEM_Q - 1)))))
;  // clang-format on

#define indcpa_keypair_derand MLKEM_NAMESPACE(indcpa_keypair_derand)
void indcpa_keypair_derand(uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                           uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES],
                           const uint8_t coins[MLKEM_SYMBYTES])
    // clang-format off
  REQUIRES(IS_FRESH(pk, MLKEM_INDCPA_PUBLICKEYBYTES))
  REQUIRES(IS_FRESH(sk, MLKEM_INDCPA_SECRETKEYBYTES))
  REQUIRES(IS_FRESH(coins, MLKEM_SYMBYTES))
  ASSIGNS(OBJECT_WHOLE(pk))
  ASSIGNS(OBJECT_WHOLE(sk));
// clang-format on

#define indcpa_enc MLKEM_NAMESPACE(indcpa_enc)
void indcpa_enc(uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t pk[MLKEM_INDCPA_PUBLICKEYBYTES],
                const uint8_t coins[MLKEM_SYMBYTES]);

#define indcpa_dec MLKEM_NAMESPACE(indcpa_dec)
void indcpa_dec(uint8_t m[MLKEM_INDCPA_MSGBYTES],
                const uint8_t c[MLKEM_INDCPA_BYTES],
                const uint8_t sk[MLKEM_INDCPA_SECRETKEYBYTES]);

#endif
