/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef POLY_H
#define POLY_H

#include <stddef.h>
#include <stdint.h>
#include "cbmc.h"
#include "common.h"
#include "debug.h"
#include "verify.h"

/* Absolute exclusive upper bound for the output of the inverse NTT */
#define INVNTT_BOUND (8 * MLKEM_Q)

/* Absolute exclusive upper bound for the output of the forward NTT */
#define NTT_BOUND (8 * MLKEM_Q)

#define zetas MLKEM_NAMESPACE(zetas)
extern const int16_t zetas[128];

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
#define poly MLKEM_NAMESPACE(poly)
typedef struct
{
  int16_t coeffs[MLKEM_N];
} ALIGN poly;

/*
 * INTERNAL presentation of precomputed data speeding up
 * the base multiplication of two polynomials in NTT domain.
 */
#define poly_mulcache MLKEM_NAMESPACE(poly_mulcache)
typedef struct
{
  int16_t coeffs[MLKEM_N >> 1];
} poly_mulcache;

#define poly_basemul_montgomery_cached \
  MLKEM_NAMESPACE(poly_basemul_montgomery_cached)
/*************************************************
 * Name:        poly_basemul_montgomery_cached
 *
 * Description: Multiplication of two polynomials in NTT domain,
 *              using mulcache for second operand.
 *
 *              Bounds:
 *              - a is assumed to be coefficient-wise < q in absolute value.
 *
 *              The result is coefficient-wise bound by 2*q in absolute value.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const poly *a: pointer to first input polynomial
 *              - const poly *b: pointer to second input polynomial
 *              - const poly_mulcache *b_cache: pointer to mulcache
 *                  for second input polynomial. Can be computed
 *                  via poly_mulcache_compute().
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_basemul_montgomery_cached(poly *r, const poly *a, const poly *b,
                                    const poly_mulcache *b_cache)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(memory_no_alias(b, sizeof(poly)))
  requires(memory_no_alias(b_cache, sizeof(poly_mulcache)))
  requires(array_bound(a->coeffs, 0, MLKEM_N, 0, UINT12_LIMIT))
  assigns(object_whole(r))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, 2 * MLKEM_Q))
);

#define poly_tomont MLKEM_NAMESPACE(poly_tomont)
/*************************************************
 * Name:        poly_tomont
 *
 * Description: Inplace conversion of all coefficients of a polynomial
 *              from normal domain to Montgomery domain
 *
 *              Bounds: Output < q in absolute value.
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_tomont(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_Q))
);

#define poly_mulcache_compute MLKEM_NAMESPACE(poly_mulcache_compute)
/************************************************************
 * Name: poly_mulcache_compute
 *
 * Description: Computes the mulcache for a polynomial in NTT domain
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
 * Arguments: - x: Pointer to mulcache to be populated
 *            - a: Pointer to input polynomial
 ************************************************************/
/*
 * NOTE: The default C implementation of this function populates
 * the mulcache with values in (-q,q), but this is not needed for the
 * higher level safety proofs, and thus not part of the spec.
 */
MLKEM_NATIVE_INTERNAL_API
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
__contract__(
  requires(memory_no_alias(x, sizeof(poly_mulcache)))
  requires(memory_no_alias(a, sizeof(poly)))
  assigns(object_whole(x))
);

#define poly_reduce MLKEM_NAMESPACE(poly_reduce)
/*************************************************
 * Name:        poly_reduce
 *
 * Description: Converts polynomial to _unsigned canonical_ representatives.
 *
 *              The input coefficients can be arbitrary integers in int16_t.
 *              The output coefficients are in [0,1,...,MLKEM_Q-1].
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
/*
 * NOTE: The semantics of poly_reduce() is different in
 * the reference implementation, which requires
 * signed canonical output data. Unsigned canonical
 * outputs are better suited to the only remaining
 * use of poly_reduce() in the context of (de)serialization.
 */
MLKEM_NATIVE_INTERNAL_API
void poly_reduce(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_bound(r->coeffs, 0, MLKEM_N, 0, MLKEM_Q))
);

#define poly_add MLKEM_NAMESPACE(poly_add)
/************************************************************
 * Name: poly_add
 *
 * Description: Adds two polynomials in place
 *
 * Arguments: - r: Pointer to input-output polynomial to be added to.
 *            - b: Pointer to input polynomial that should be added
 *                 to r. Must be disjoint from r.
 *
 * The coefficients of r and b must be so that the addition does
 * not overflow. Otherwise, the behaviour of this function is undefined.
 *
 ************************************************************/
/*
 * NOTE: The reference implementation uses a 3-argument poly_add.
 * We specialize to the accumulator form to avoid reasoning about aliasing.
 */
MLKEM_NATIVE_INTERNAL_API
void poly_add(poly *r, const poly *b)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(b, sizeof(poly)))
  requires(forall(k0, 0, MLKEM_N, (int32_t) r->coeffs[k0] + b->coeffs[k0] <= INT16_MAX))
  requires(forall(k1, 0, MLKEM_N, (int32_t) r->coeffs[k1] + b->coeffs[k1] >= INT16_MIN))
  ensures(forall(k, 0, MLKEM_N, r->coeffs[k] == old(*r).coeffs[k] + b->coeffs[k]))
  assigns(memory_slice(r, sizeof(poly)))
);

#define poly_sub MLKEM_NAMESPACE(poly_sub)
/*************************************************
 * Name:        poly_sub
 *
 * Description: Subtract two polynomials; no modular reduction is performed
 *
 * Arguments: - poly *r:       Pointer to input-output polynomial to be added
 *to.
 *            - const poly *b: Pointer to second input polynomial
 **************************************************/
/*
 * NOTE: The reference implementation uses a 3-argument poly_sub.
 * We specialize to the accumulator form to avoid reasoning about aliasing.
 */
MLKEM_NATIVE_INTERNAL_API
void poly_sub(poly *r, const poly *b)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(b, sizeof(poly)))
  requires(forall(k0, 0, MLKEM_N, (int32_t) r->coeffs[k0] - b->coeffs[k0] <= INT16_MAX))
  requires(forall(k1, 0, MLKEM_N, (int32_t) r->coeffs[k1] - b->coeffs[k1] >= INT16_MIN))
  ensures(forall(k, 0, MLKEM_N, r->coeffs[k] == old(*r).coeffs[k] - b->coeffs[k]))
  assigns(object_whole(r))
);

#define poly_ntt MLKEM_NAMESPACE(poly_ntt)
/*************************************************
 * Name:        poly_ntt
 *
 * Description: Computes negacyclic number-theoretic transform (NTT) of
 *              a polynomial in place.
 *
 *              The input is assumed to be in normal order and
 *              coefficient-wise bound by MLKEM_Q in absolute value.
 *
 *              The output polynomial is in bitreversed order, and
 *              coefficient-wise bound by NTT_BOUND in absolute value.
 *
 *              (NOTE: Sometimes the input to the NTT is actually smaller,
 *               which gives better bounds.)
 *
 * Arguments:   - poly *p: pointer to in/output polynomial
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_ntt(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, NTT_BOUND))
);

#define poly_invntt_tomont MLKEM_NAMESPACE(poly_invntt_tomont)
/*************************************************
 * Name:        poly_invntt_tomont
 *
 * Description: Computes inverse of negacyclic number-theoretic transform (NTT)
 *              of a polynomial in place;
 *              inputs assumed to be in bitreversed order, output in normal
 *              order
 *
 *              The input is assumed to be in bitreversed order, and can
 *              have arbitrary coefficients in int16_t.
 *
 *              The output polynomial is in normal order, and
 *              coefficient-wise bound by INVNTT_BOUND in absolute value.
 *
 * Arguments:   - uint16_t *a: pointer to in/output polynomial
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_invntt_tomont(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, INVNTT_BOUND))
);

/* Static namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define scalar_compress_d1 MLKEM_NAMESPACE(scalar_compress_d1)
#define scalar_compress_d4 MLKEM_NAMESPACE(scalar_compress_d4)
#define scalar_compress_d5 MLKEM_NAMESPACE(scalar_compress_d5)
#define scalar_compress_d10 MLKEM_NAMESPACE(scalar_compress_d10)
#define scalar_compress_d11 MLKEM_NAMESPACE(scalar_compress_d11)
#define scalar_decompress_d4 MLKEM_NAMESPACE(scalar_decompress_d4)
#define scalar_decompress_d5 MLKEM_NAMESPACE(scalar_decompress_d5)
#define scalar_decompress_d10 MLKEM_NAMESPACE(scalar_decompress_d10)
#define scalar_decompress_d11 MLKEM_NAMESPACE(scalar_decompress_d11)
/* End of static namespacing */

/************************************************************
 * Name: scalar_compress_d1
 *
 * Description: Computes round(u * 2 / q)
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 1.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
/*
 * The multiplication in this routine will exceed UINT32_MAX
 * and wrap around for large values of u. This is expected and required.
 */
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static INLINE uint32_t scalar_compress_d1(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < 2)
  ensures(return_value == (((uint32_t)u * 2 + MLKEM_Q / 2) / MLKEM_Q) % 2)  )
{
  uint32_t d0 = u << 1;
  d0 *= 645083;
  d0 += 1u << 30;
  d0 >>= 31;
  return d0;
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_compress_d4
 *
 * Description: Computes round(u * 16 / q) % 16
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 4.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
/*
 * The multiplication in this routine will exceed UINT32_MAX
 * and wrap around for large values of u. This is expected and required.
 */
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static INLINE uint32_t scalar_compress_d4(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < 16)
  ensures(return_value == (((uint32_t)u * 16 + MLKEM_Q / 2) / MLKEM_Q) % 16))
{
  uint32_t d0 = (uint32_t)u * 1290160; /* 16 * round(2^28 / MLKEM_Q) */
  return (d0 + (1u << 27)) >> 28;      /* round(d0/2^28) */
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d4
 *
 * Description: Computes round(u * q / 16)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 4.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 16
 *                 to be decompressed.
 ************************************************************/
static INLINE uint16_t scalar_decompress_d4(uint32_t u)
__contract__(
  requires(0 <= u && u < 16)
  ensures(return_value <= (MLKEM_Q - 1))
) { return ((u * MLKEM_Q) + 8) >> 4; }

/************************************************************
 * Name: scalar_compress_d5
 *
 * Description: Computes round(u * 32 / q) % 32
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 5.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
/*
 * The multiplication in this routine will exceed UINT32_MAX
 * and wrap around for large values of u. This is expected and required.
 */
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static INLINE uint32_t scalar_compress_d5(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < 32)
  ensures(return_value == (((uint32_t)u * 32 + MLKEM_Q / 2) / MLKEM_Q) % 32)  )
{
  uint32_t d0 = (uint32_t)u * 1290176; /* 2^5 * round(2^27 / MLKEM_Q) */
  return (d0 + (1u << 26)) >> 27;      /* round(d0/2^27) */
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d5
 *
 * Description: Computes round(u * q / 32)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 5.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 32
 *                 to be decompressed.
 ************************************************************/
static INLINE uint16_t scalar_decompress_d5(uint32_t u)
__contract__(
  requires(0 <= u && u < 32)
  ensures(return_value <= MLKEM_Q - 1)
) { return ((u * MLKEM_Q) + 16) >> 5; }

/************************************************************
 * Name: scalar_compress_d10
 *
 * Description: Computes round(u * 2**10 / q) % 2**10
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 10.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
/*
 * The multiplication in this routine will exceed UINT32_MAX
 * and wrap around for large values of u. This is expected and required.
 */
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static INLINE uint32_t scalar_compress_d10(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < (1u << 10))
  ensures(return_value == (((uint32_t)u * (1u << 10) + MLKEM_Q / 2) / MLKEM_Q) % (1 << 10)))
{
  uint64_t d0 = (uint64_t)u * 2642263040; /* 2^10 * round(2^32 / MLKEM_Q) */
  d0 = (d0 + ((uint64_t)1u << 32)) >> 33;
  return (d0 & 0x3FF);
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d10
 *
 * Description: Computes round(u * q / 1024)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 10.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 16
 *                 to be decompressed.
 ************************************************************/
static INLINE uint16_t scalar_decompress_d10(uint32_t u)
__contract__(
  requires(0 <= u && u < 1024)
  ensures(return_value <= (MLKEM_Q - 1))
) { return ((u * MLKEM_Q) + 512) >> 10; }

/************************************************************
 * Name: scalar_compress_d11
 *
 * Description: Computes round(u * 2**11 / q) % 2**11
 *
 *              Implements Compress_d from FIPS203, Eq (4.7),
 *              for d = 11.
 *
 * Arguments: - u: Unsigned canonical modulus modulo q
 *                 to be compressed.
 ************************************************************/
/*
 * The multiplication in this routine will exceed UINT32_MAX
 * and wrap around for large values of u. This is expected and required.
 */
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static INLINE uint32_t scalar_compress_d11(uint16_t u)
__contract__(
  requires(u <= MLKEM_Q - 1)
  ensures(return_value < (1u << 11))
  ensures(return_value == (((uint32_t)u * (1u << 11) + MLKEM_Q / 2) / MLKEM_Q) % (1 << 11)))
{
  uint64_t d0 = (uint64_t)u * 5284526080; /* 2^11 * round(2^33 / MLKEM_Q) */
  d0 = (d0 + ((uint64_t)1u << 32)) >> 33;
  return (d0 & 0x7FF);
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/************************************************************
 * Name: scalar_decompress_d11
 *
 * Description: Computes round(u * q / 1024)
 *
 *              Implements Decompress_d from FIPS203, Eq (4.8),
 *              for d = 10.
 *
 * Arguments: - u: Unsigned canonical modulus modulo 16
 *                 to be decompressed.
 ************************************************************/
static INLINE uint16_t scalar_decompress_d11(uint32_t u)
__contract__(
  requires(0 <= u && u < 2048)
  ensures(return_value <= (MLKEM_Q - 1))
) { return ((u * MLKEM_Q) + 1024) >> 11; }

#if defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || \
    (MLKEM_K == 2 || MLKEM_K == 3)
#define poly_compress_d4 MLKEM_NAMESPACE(poly_compress_d4)
/*************************************************
 * Name:        poly_compress_d4
 *
 * Description: Compression (4 bits) and subsequent serialization of a
 *              polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D4 bytes)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,MLKEM_Q-1].
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_compress_d4(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D4], const poly *a);

#define poly_compress_d10 MLKEM_NAMESPACE(poly_compress_d10)
/*************************************************
 * Name:        poly_compress_d10
 *
 * Description: Compression (10 bits) and subsequent serialization of a
 *              polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D10 bytes)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,MLKEM_Q-1].
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_compress_d10(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D10], const poly *a);

#define poly_decompress_d4 MLKEM_NAMESPACE(poly_decompress_d4)
/*************************************************
 * Name:        poly_decompress_d4
 *
 * Description: De-serialization and subsequent decompression (dv bits) of a
 *              polynomial; approximate inverse of poly_compress
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D4 bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than MLKEM_Q).
 *
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d4(poly *r, const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D4]);

#define poly_decompress_d10 MLKEM_NAMESPACE(poly_decompress_d10)
/*************************************************
 * Name:        poly_decompress_d10
 *
 * Description: De-serialization and subsequent decompression (10 bits) of a
 *              polynomial; approximate inverse of poly_compress_d10
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D10 bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than MLKEM_Q).
 *
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d10(poly *r,
                         const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D10]);
#endif /* defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || (MLKEM_K == 2 \
          || MLKEM_K == 3) */

#if defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || MLKEM_K == 4
#define poly_compress_d5 MLKEM_NAMESPACE(poly_compress_d5)
/*************************************************
 * Name:        poly_compress_d5
 *
 * Description: Compression (5 bits) and subsequent serialization of a
 *              polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D5 bytes)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,MLKEM_Q-1].
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_compress_d5(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D5], const poly *a);

#define poly_compress_d11 MLKEM_NAMESPACE(poly_compress_d11)
/*************************************************
 * Name:        poly_compress_d11
 *
 * Description: Compression (11 bits) and subsequent serialization of a
 *              polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D11 bytes)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,MLKEM_Q-1].
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_compress_d11(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES_D11], const poly *a);

#define poly_decompress_d5 MLKEM_NAMESPACE(poly_decompress_d5)
/*************************************************
 * Name:        poly_decompress_d5
 *
 * Description: De-serialization and subsequent decompression (dv bits) of a
 *              polynomial; approximate inverse of poly_compress
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D5 bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than MLKEM_Q).
 *
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d5(poly *r, const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D5]);

#define poly_decompress_d11 MLKEM_NAMESPACE(poly_decompress_d11)
/*************************************************
 * Name:        poly_decompress_d11
 *
 * Description: De-serialization and subsequent decompression (11 bits) of a
 *              polynomial; approximate inverse of poly_compress_d11
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                   (of length MLKEM_POLYCOMPRESSEDBYTES_D11 bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than MLKEM_Q).
 *
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_decompress_d11(poly *r,
                         const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES_D11]);
#endif /* defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || MLKEM_K == 4 \
        */

#define poly_tobytes MLKEM_NAMESPACE(poly_tobytes)
/*************************************************
 * Name:        poly_tobytes
 *
 * Description: Serialization of a polynomial.
 *              Signed coefficients are converted to
 *              unsigned form before serialization.
 *
 * Arguments:   INPUT:
 *              - a: const pointer to input polynomial,
 *                with each coefficient in the range [0,1,..,Q-1]
 *              OUTPUT
 *              - r: pointer to output byte array
 *                   (of MLKEM_POLYBYTES bytes)
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_tobytes(uint8_t r[MLKEM_POLYBYTES], const poly *a)
__contract__(
  requires(memory_no_alias(r, MLKEM_POLYBYTES))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(array_bound(a->coeffs, 0, MLKEM_N, 0, MLKEM_Q))
  assigns(object_whole(r))
);


#define poly_frombytes MLKEM_NAMESPACE(poly_frombytes)
/*************************************************
 * Name:        poly_frombytes
 *
 * Description: De-serialization of a polynomial.
 *
 * Arguments:   INPUT
 *              - a: pointer to input byte array
 *                   (of MLKEM_POLYBYTES bytes)
 *              OUTPUT
 *              - r: pointer to output polynomial, with
 *                   each coefficient unsigned and in the range
 *                   0 .. 4095
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_frombytes(poly *r, const uint8_t a[MLKEM_POLYBYTES])
__contract__(
  requires(memory_no_alias(a, MLKEM_POLYBYTES))
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_bound(r->coeffs, 0, MLKEM_N, 0, UINT12_LIMIT))
);


#define poly_frommsg MLKEM_NAMESPACE(poly_frommsg)
/*************************************************
 * Name:        poly_frommsg
 *
 * Description: Convert 32-byte message to polynomial
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *msg: pointer to input message
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_frommsg(poly *r, const uint8_t msg[MLKEM_INDCPA_MSGBYTES])
__contract__(
  requires(memory_no_alias(msg, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(object_whole(r))
  ensures(array_bound(r->coeffs, 0, MLKEM_N, 0, MLKEM_Q))
);

#define poly_tomsg MLKEM_NAMESPACE(poly_tomsg)
/*************************************************
 * Name:        poly_tomsg
 *
 * Description: Convert polynomial to 32-byte message
 *
 * Arguments:   - uint8_t *msg: pointer to output message
 *              - const poly *r: pointer to input polynomial
 *                Coefficients must be unsigned canonical
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_tomsg(uint8_t msg[MLKEM_INDCPA_MSGBYTES], const poly *r)
__contract__(
  requires(memory_no_alias(msg, MLKEM_INDCPA_MSGBYTES))
  requires(memory_no_alias(r, sizeof(poly)))
  requires(array_bound(r->coeffs, 0, MLKEM_N, 0, MLKEM_Q))
  assigns(object_whole(msg))
);

#define poly_cbd2 MLKEM_NAMESPACE(poly_cbd2)
/*************************************************
 * Name:        poly_cbd2
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter eta=2
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_cbd2(poly *r, const uint8_t buf[2 * MLKEM_N / 4]);

#if defined(MLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED) || MLKEM_ETA1 == 3
#define poly_cbd3 MLKEM_NAMESPACE(poly_cbd3)
/*************************************************
 * Name:        poly_cbd3
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter eta=3.
 *              This function is only needed for ML-KEM-512
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_cbd3(poly *r, const uint8_t buf[3 * MLKEM_N / 4]);
#endif /* MLKEM_NATIVE_MULTILEVEL_BUILD || MLKEM_ETA1 == 3 */

#define poly_rej_uniform_x4 MLKEM_NAMESPACE(poly_rej_uniform_x4)
/*************************************************
 * Name:        poly_rej_uniform_x4
 *
 * Description: Generate four polynomials using rejection sampling
 *              on (pseudo-)uniformly random bytes sampled from a seed.
 *
 * Arguments:   - poly *vec:           Pointer to an array of 4 polynomials
 *                                     to be sampled.
 *              - uint8_t *seed[4]:    Pointer to array of four pointers
 *                                     pointing to the seed buffers of size
 *                                     MLKEM_SYMBYTES + 2 each.
 *
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_rej_uniform_x4(poly *vec, uint8_t *seed[4])
__contract__(
  requires(memory_no_alias(vec, sizeof(poly) * 4))
  requires(memory_no_alias(seed, sizeof(uint8_t*) * 4))
  requires(memory_no_alias(seed[0], MLKEM_SYMBYTES + 2))
  requires(memory_no_alias(seed[1], MLKEM_SYMBYTES + 2))
  requires(memory_no_alias(seed[2], MLKEM_SYMBYTES + 2))
  requires(memory_no_alias(seed[3], MLKEM_SYMBYTES + 2))
  assigns(memory_slice(vec, sizeof(poly) * 4))
  ensures(array_bound(vec[0].coeffs, 0, MLKEM_N, 0, MLKEM_Q))
  ensures(array_bound(vec[1].coeffs, 0, MLKEM_N, 0, MLKEM_Q))
  ensures(array_bound(vec[2].coeffs, 0, MLKEM_N, 0, MLKEM_Q))
  ensures(array_bound(vec[3].coeffs, 0, MLKEM_N, 0, MLKEM_Q)));

#define poly_rej_uniform MLKEM_NAMESPACE(poly_rej_uniform)
/*************************************************
 * Name:        poly_rej_uniform
 *
 * Description: Generate polynomial using rejection sampling
 *              on (pseudo-)uniformly random bytes sampled from a seed.
 *
 * Arguments:   - poly *vec:           Pointer to polynomial to be sampled.
 *              - uint8_t *seed:       Pointer to seed buffer of size
 *                                     MLKEM_SYMBYTES + 2 each.
 *
 **************************************************/
MLKEM_NATIVE_INTERNAL_API
void poly_rej_uniform(poly *entry, uint8_t seed[MLKEM_SYMBYTES + 2])
__contract__(
  requires(memory_no_alias(entry, sizeof(poly)))
  requires(memory_no_alias(seed, MLKEM_SYMBYTES + 2))
  assigns(memory_slice(entry, sizeof(poly)))
  ensures(array_bound(entry->coeffs, 0, MLKEM_N, 0, MLKEM_Q)));

#endif /* POLY_H */
