// SPDX-License-Identifier: Apache-2.0
#include "polyvec.h"
#include <stdint.h>
#include "arith_native.h"
#include "config.h"
#include "ntt.h"
#include "params.h"
#include "poly.h"

#include "debug/debug.h"
/*************************************************
 * Name:        polyvec_compress
 *
 * Description: Compress and serialize vector of polynomials
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                            (needs space for MLKEM_POLYVECCOMPRESSEDBYTES)
 *              - const polyvec *a: pointer to input vector of polynomials
 **************************************************/
void polyvec_compress(uint8_t r[MLKEM_POLYVECCOMPRESSEDBYTES],
                      const polyvec *a) {
  POLYVEC_UBOUND(a, MLKEM_Q);
  unsigned int i, j, k;

#if (MLKEM_POLYVECCOMPRESSEDBYTES == (MLKEM_K * 352))
  uint16_t t[8];
  for (i = 0; i < MLKEM_K; i++) {
    for (j = 0; j < MLKEM_N / 8; j++) {
      for (k = 0; k < 8; k++) {
        t[k] = scalar_compress_d11(a->vec[i].coeffs[8 * j + k]);
      }

      r[0] = (t[0] >> 0);
      r[1] = (t[0] >> 8) | (t[1] << 3);
      r[2] = (t[1] >> 5) | (t[2] << 6);
      r[3] = (t[2] >> 2);
      r[4] = (t[2] >> 10) | (t[3] << 1);
      r[5] = (t[3] >> 7) | (t[4] << 4);
      r[6] = (t[4] >> 4) | (t[5] << 7);
      r[7] = (t[5] >> 1);
      r[8] = (t[5] >> 9) | (t[6] << 2);
      r[9] = (t[6] >> 6) | (t[7] << 5);
      r[10] = (t[7] >> 3);
      r += 11;
    }
  }
#elif (MLKEM_POLYVECCOMPRESSEDBYTES == (MLKEM_K * 320))
  uint16_t t[4];
  for (i = 0; i < MLKEM_K; i++) {
    for (j = 0; j < MLKEM_N / 4; j++) {
      for (k = 0; k < 4; k++) {
        t[k] = scalar_compress_d10(a->vec[i].coeffs[4 * j + k]);
      }

      r[0] = (t[0] >> 0);
      r[1] = (t[0] >> 8) | (t[1] << 2);
      r[2] = (t[1] >> 6) | (t[2] << 4);
      r[3] = (t[2] >> 4) | (t[3] << 6);
      r[4] = (t[3] >> 2);
      r += 5;
    }
  }
#else
#error "MLKEM_POLYVECCOMPRESSEDBYTES needs to be in {320*MLKEM_K, 352*MLKEM_K}"
#endif
}

/*************************************************
 * Name:        polyvec_decompress
 *
 * Description: De-serialize and decompress vector of polynomials;
 *              approximate inverse of polyvec_compress
 *
 * Arguments:   - polyvec *r:       pointer to output vector of polynomials
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYVECCOMPRESSEDBYTES)
 **************************************************/
void polyvec_decompress(polyvec *r,
                        const uint8_t a[MLKEM_POLYVECCOMPRESSEDBYTES]) {
  unsigned int i, j, k;

#if (MLKEM_POLYVECCOMPRESSEDBYTES == (MLKEM_K * 352))
  uint16_t t[8];
  for (i = 0; i < MLKEM_K; i++) {
    for (j = 0; j < MLKEM_N / 8; j++) {
      t[0] = (a[0] >> 0) | ((uint16_t)a[1] << 8);
      t[1] = (a[1] >> 3) | ((uint16_t)a[2] << 5);
      t[2] = (a[2] >> 6) | ((uint16_t)a[3] << 2) | ((uint16_t)a[4] << 10);
      t[3] = (a[4] >> 1) | ((uint16_t)a[5] << 7);
      t[4] = (a[5] >> 4) | ((uint16_t)a[6] << 4);
      t[5] = (a[6] >> 7) | ((uint16_t)a[7] << 1) | ((uint16_t)a[8] << 9);
      t[6] = (a[8] >> 2) | ((uint16_t)a[9] << 6);
      t[7] = (a[9] >> 5) | ((uint16_t)a[10] << 3);
      a += 11;

      for (k = 0; k < 8; k++) {
        r->vec[i].coeffs[8 * j + k] =
            ((uint32_t)(t[k] & 0x7FF) * MLKEM_Q + 1024) >> 11;
      }
    }
  }
#elif (MLKEM_POLYVECCOMPRESSEDBYTES == (MLKEM_K * 320))
  uint16_t t[4];
  for (i = 0; i < MLKEM_K; i++) {
    for (j = 0; j < MLKEM_N / 4; j++) {
      t[0] = (a[0] >> 0) | ((uint16_t)a[1] << 8);
      t[1] = (a[1] >> 2) | ((uint16_t)a[2] << 6);
      t[2] = (a[2] >> 4) | ((uint16_t)a[3] << 4);
      t[3] = (a[3] >> 6) | ((uint16_t)a[4] << 2);
      a += 5;

      for (k = 0; k < 4; k++) {
        r->vec[i].coeffs[4 * j + k] =
            ((uint32_t)(t[k] & 0x3FF) * MLKEM_Q + 512) >> 10;
      }
    }
  }
#else
#error "MLKEM_POLYVECCOMPRESSEDBYTES needs to be in {320*MLKEM_K, 352*MLKEM_K}"
#endif

  POLYVEC_UBOUND(r, MLKEM_Q);
}

void polyvec_tobytes(uint8_t r[MLKEM_POLYVECBYTES], const polyvec *a) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++)  // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(r))
    INVARIANT(i <= MLKEM_K)  // clang-format on
    {
      poly_tobytes(r + i * MLKEM_POLYBYTES, &a->vec[i]);
    }
}

void polyvec_frombytes(polyvec *r, const uint8_t a[MLKEM_POLYVECBYTES]) {
  int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_frombytes(&r->vec[i], a + i * MLKEM_POLYBYTES);
  }
}

/*************************************************
 * Name:        polyvec_ntt
 *
 * Description: Apply forward NTT to all elements of a vector of polynomials
 *
 * Arguments:   - polyvec *r: pointer to in/output vector of polynomials
 **************************************************/
void polyvec_ntt(polyvec *r) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_ntt(&r->vec[i]);
  }
}

/*************************************************
 * Name:        polyvec_invntt_tomont
 *
 * Description: Apply inverse NTT to all elements of a vector of polynomials
 *              and multiply by Montgomery factor 2^16
 *
 * Arguments:   - polyvec *r: pointer to in/output vector of polynomials
 **************************************************/
void polyvec_invntt_tomont(polyvec *r) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_invntt_tomont(&r->vec[i]);
  }
}

/*************************************************
 * Name:        polyvec_basemul_acc_montgomery
 *
 * Description: Multiply elements of a and b in NTT domain, accumulate into r,
 *              and multiply by 2^-16.
 *
 *              Bounds:
 *              - a is assumed to be coefficient-wise < q in absolute value.
 *              - b is assumed to be the output of a forward NTT and
 *                thus coefficient-wise bound by NTT_BOUND
 *              - b_cache is assumed to be coefficient-wise bound by
 *                MLKEM_Q.
 *
 * Arguments: - poly *r: pointer to output polynomial
 *            - const polyvec *a: pointer to first input vector of polynomials
 *            - const polyvec *b: pointer to second input vector of polynomials
 *            - const polyvec_mulcache *b_cache: mulcache for b
 **************************************************/
#if !defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache) {
  POLYVEC_BOUND(a, MLKEM_Q);
  POLYVEC_BOUND(b, NTT_BOUND);
  POLYVEC_BOUND(b_cache, MLKEM_Q);

  int i;
  poly t;

  poly_basemul_montgomery_cached(r, &a->vec[0], &b->vec[0], &b_cache->vec[0]);

  for (i = 1; i < MLKEM_K; i++)
      // clang-format off
    ASSIGNS(i, t, OBJECT_WHOLE(r))
    INVARIANT(i >= 1 && i <= MLKEM_K)
    INVARIANT(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs,
                              i * (-3 * HALF_Q + 1), i * (3 * HALF_Q - 1)))
    DECREASES(MLKEM_K - i)
    // clang-format on
    {
      poly_basemul_montgomery_cached(&t, &a->vec[i], &b->vec[i],
                                     &b_cache->vec[i]);
      poly_add(r, &t);
      // abs bounds: < (i+1) * 3/2 * q
    }

  // Those bounds are true for the C implementation, but not needed
  // in the higher level bounds reasoning. It is thus best to omit
  // them from the spec to not unnecessarily constraint native implementations.
  ASSERT(
      ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs,
                      MLKEM_K * (-3 * HALF_Q + 1), MLKEM_K * (3 * HALF_Q - 1)),
      "polyvec_basemul_acc_montgomery_cached output bounds");
  // TODO: Integrate CBMC assertion into POLY_BOUND if CBMC is set
  POLY_BOUND(r, MLKEM_K * 3 * HALF_Q);
}
#else  /* !MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */
void polyvec_basemul_acc_montgomery_cached(poly *r, const polyvec *a,
                                           const polyvec *b,
                                           const polyvec_mulcache *b_cache) {
  POLYVEC_BOUND(a, MLKEM_Q);
  POLYVEC_BOUND(b, NTT_BOUND);
  POLYVEC_BOUND(b_cache, MLKEM_Q);
  polyvec_basemul_acc_montgomery_cached_native(r, a, b, b_cache);
}
#endif /* MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED */

/*************************************************
 * Name:        polyvec_basemul_acc_montgomery
 *
 * Description: Multiply elements of a and b in NTT domain, accumulate into r,
 *              and multiply by 2^-16.
 *
 * Arguments: - poly *r: pointer to output polynomial
 *            - const polyvec *a: pointer to first input vector of polynomials
 *            - const polyvec *b: pointer to second input vector of polynomials
 **************************************************/
void polyvec_basemul_acc_montgomery(poly *r, const polyvec *a,
                                    const polyvec *b) {
  polyvec_mulcache b_cache;
  polyvec_mulcache_compute(&b_cache, b);
  polyvec_basemul_acc_montgomery_cached(r, a, b, &b_cache);
}

/*************************************************
 * Name:        polyvec_mulcache_compute
 *
 * Description: Precompute values speeding up
 *              base multiplications of polynomials
 *              in NTT domain.
 *
 * Arguments: - polyvec_mulcache *x: pointer to output cache.
 *            - const poly *a: pointer to input polynomial
 **************************************************/
void polyvec_mulcache_compute(polyvec_mulcache *x, const polyvec *a) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_mulcache_compute(&x->vec[i], &a->vec[i]);
  }
}


/*************************************************
 * Name:        polyvec_reduce
 *
 * Description: Applies Barrett reduction to each coefficient
 *              of each element of a vector of polynomials;
 *              for details of the Barrett reduction see comments in reduce.c
 *
 * Arguments:   - polyvec *r: pointer to input/output polynomial
 **************************************************/
void polyvec_reduce(polyvec *r) {
  unsigned int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_reduce(&r->vec[i]);
  }
}

void polyvec_add(polyvec *r, const polyvec *b) {
  int i;
  for (i = 0; i < MLKEM_K; i++) {
    poly_add(&r->vec[i], &b->vec[i]);
  }
}
