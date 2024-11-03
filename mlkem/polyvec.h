// SPDX-License-Identifier: Apache-2.0
#ifndef POLYVEC_H
#define POLYVEC_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

typedef struct {
  poly vec[MLKEM_K];
} ALIGN polyvec;

// REF-CHANGE: This struct does not exist in the reference implementation
typedef struct {
  poly_mulcache vec[MLKEM_K];
} polyvec_mulcache;

#define polyvec_compress MLKEM_NAMESPACE(polyvec_compress)
void polyvec_compress(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES+2],
                      const polyvec *a);
#define polyvec_decompress MLKEM_NAMESPACE(polyvec_decompress)
void polyvec_decompress(polyvec *r,
                        const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES+12]);

#define polyvec_tobytes MLKEM_NAMESPACE(polyvec_tobytes)
void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES], const polyvec *a);
#define polyvec_frombytes MLKEM_NAMESPACE(polyvec_frombytes)
void polyvec_frombytes(polyvec *r, const uint8_t a[MLKEM_POLYVECBYTES]);

#define polyvec_ntt MLKEM_NAMESPACE(polyvec_ntt)
void polyvec_ntt(polyvec *r);
#define polyvec_invntt_tomont MLKEM_NAMESPACE(polyvec_invntt_tomont)
void polyvec_invntt_tomont(polyvec *r);

#define polyvec_basemul_acc_montgomery \
  MLKEM_NAMESPACE(polyvec_basemul_acc_montgomery)
void polyvec_basemul_acc_montgomery(poly *r, const polyvec *a,
                                    const polyvec *b);

// REF-CHANGE: This function does not exist in the reference implementation
#define polyvec_basemul_acc_montgomery_cached \
  MLKEM_NAMESPACE(polyvec_basemul_acc_montgomery_cached)
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache);

// REF-CHANGE: This function does not exist in the reference implementation
#define polyvec_mulcache_compute MLKEM_NAMESPACE(polyvec_mulcache_compute)
/************************************************************
 * Name: polyvec_mulcache_compute
 *
 * Description: Computes the mulcache for a vector of polynomials in NTT domain
 *
 *              The mulcache of a degree-2 polynomial b := b0 + b1*X
 *              in Fq[X]/(X^2-zeta) is the value b1*zeta, needed when
 *              computing products of b in Fq[X]/(X^2-zeta).
 *
 *              The mulcache of a polynomial in NTT domain -- which is
 *              a 128-tuple of degree-2 polynomials in Fq[X]/(X^2-zeta),
 *              for varying zeta, is the 128-tuple of mulcaches of those
 *              polynomials.
 *
 *              The mulcache of a vector of polynomials is the vector
 *              of mulcaches of its entries.
 *
 * Arguments: - x: Pointer to mulcache to be populated
 *            - a: Pointer to input polynomial vector
 ************************************************************/
// NOTE: The default C implementation of this function populates
// the mulcache with values in (-q,q), but this is not needed for the
// higher level safety proofs, and thus not part of the spec.
void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a)
    // clang-format off
REQUIRES(a != NULL && IS_FRESH(a, sizeof(polyvec)))
ASSIGNS(OBJECT_WHOLE(x));
// clang-format on

#define polyvec_reduce MLKEM_NAMESPACE(polyvec_reduce)
void polyvec_reduce(polyvec *r);

#define polyvec_add MLKEM_NAMESPACE(polyvec_add)
void polyvec_add(polyvec *r, const polyvec *a, const polyvec *b);

#endif
