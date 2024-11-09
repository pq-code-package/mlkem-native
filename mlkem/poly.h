// SPDX-License-Identifier: Apache-2.0
#ifndef POLY_H
#define POLY_H

#include <stddef.h>
#include <stdint.h>
#include "cbmc.h"
#include "params.h"
#include "reduce.h"
#include "verify.h"

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct {
  int16_t coeffs[MLKEM_N];
} ALIGN poly;

/*
 * INTERNAL presentation of precomputed data speeding up
 * the base multiplication of two polynomials in NTT domain.
 */
// REF-CHANGE: This structure does not exist in the reference
// implementation.
typedef struct {
  int16_t coeffs[MLKEM_N >> 1];
} poly_mulcache;

#define scalar_compress_d1 MLKEM_NAMESPACE(scalar_compress_d1)
#define scalar_compress_d4 MLKEM_NAMESPACE(scalar_compress_d4)
#define scalar_compress_d5 MLKEM_NAMESPACE(scalar_compress_d5)
#define scalar_compress_d10 MLKEM_NAMESPACE(scalar_compress_d10)
#define scalar_compress_d11 MLKEM_NAMESPACE(scalar_compress_d11)
#define scalar_decompress_d4 MLKEM_NAMESPACE(scalar_decompress_d4)
#define scalar_decompress_d5 MLKEM_NAMESPACE(scalar_decompress_d5)
#define scalar_decompress_d10 MLKEM_NAMESPACE(scalar_decompress_d10)
#define scalar_decompress_d11 MLKEM_NAMESPACE(scalar_decompress_d11)
#define scalar_signed_to_unsigned_q MLKEM_NAMESPACE(scalar_signed_to_unsigned_q)

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
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static inline uint32_t scalar_compress_d1(uint16_t u)  // clang-format off
  REQUIRES(u <= MLKEM_Q - 1)
  ENSURES(RETURN_VALUE < 2)
  ENSURES(RETURN_VALUE == (((uint32_t)u * 2 + MLKEM_Q / 2) / MLKEM_Q) % 2)  // clang-format on
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
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static inline uint32_t scalar_compress_d4(uint16_t u)  // clang-format off
  REQUIRES(u <= MLKEM_Q - 1)
  ENSURES(RETURN_VALUE < 16)
  ENSURES(RETURN_VALUE == (((uint32_t)u * 16 + MLKEM_Q / 2) / MLKEM_Q) % 16)
{  // clang-format on
  uint32_t d0 = (uint32_t)u * 1290160;     // 16 * round(2^28 / MLKEM_Q)
  return (d0 + (1u << 27)) >> 28;          // round(d0/2^28)
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
static inline uint16_t scalar_decompress_d4(uint32_t u)  // clang-format off
  REQUIRES(0 <= u && u < 16)
  ENSURES(RETURN_VALUE <= (MLKEM_Q - 1))
{  // clang-format on
  return ((u * MLKEM_Q) + 8) / 16;
}

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
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
static inline uint32_t scalar_compress_d5(uint16_t u)  // clang-format off
  REQUIRES(u <= MLKEM_Q - 1)
  ENSURES(RETURN_VALUE < 32)
  ENSURES(RETURN_VALUE == (((uint32_t)u * 32 + MLKEM_Q / 2) / MLKEM_Q) % 32)  // clang-format on
{
  uint32_t d0 = (uint32_t)u * 1290176;  // 2^5 * round(2^27 / MLKEM_Q)
  return (d0 + (1u << 26)) >> 27;       // round(d0/2^27)
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
static inline uint16_t scalar_decompress_d5(uint32_t u)  // clang-format off
  REQUIRES(0 <= u && u < 32)
  ENSURES(RETURN_VALUE <= MLKEM_Q - 1)
{  // clang-format on
  return ((u * MLKEM_Q) + 16) / 32;
}

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
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
// TODO: do the same for the other static inline functions
STATIC_INLINE_TESTABLE
uint32_t scalar_compress_d10(uint16_t u)  // clang-format off
  REQUIRES(u <= MLKEM_Q - 1)
  ENSURES(RETURN_VALUE < (1u << 10))
  ENSURES(RETURN_VALUE == (((uint32_t)u * (1u << 10) + MLKEM_Q / 2) / MLKEM_Q) % (1 << 10))
{           // clang-format on
  uint64_t d0 = (uint64_t)u * 2642263040;  // 2^10 * round(2^32 / MLKEM_Q)
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
static inline uint16_t scalar_decompress_d10(uint32_t u)  // clang-format off
  REQUIRES(0 <= u && u < 1024)
  ENSURES(RETURN_VALUE <= (MLKEM_Q - 1))
{  // clang-format on
  return ((u * MLKEM_Q) + 512) / 1024;
}

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
// The multiplication in this routine will exceed UINT32_MAX
// and wrap around for large values of u. This is expected and required.
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "unsigned-overflow"
#endif
STATIC_INLINE_TESTABLE
uint32_t scalar_compress_d11(uint16_t u)  // clang-format off
  REQUIRES(u <= MLKEM_Q - 1)
  ENSURES(RETURN_VALUE < (1u << 11))
  ENSURES(RETURN_VALUE == (((uint32_t)u * (1u << 11) + MLKEM_Q / 2) / MLKEM_Q) % (1 << 11))
{           // clang-format on
  uint64_t d0 = (uint64_t)u * 5284526080;  // 2^11 * round(2^33 / MLKEM_Q)
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
STATIC_INLINE_TESTABLE
uint16_t scalar_decompress_d11(uint32_t u)  // clang-format off
  REQUIRES(0 <= u && u < 2048)
  ENSURES(RETURN_VALUE <= (MLKEM_Q - 1))
{  // clang-format on
  return ((u * MLKEM_Q) + 1024) / 2048;
}

/************************************************************
 * Name: scalar_signed_to_unsigned_q
 *
 * Description: converts signed polynomial coefficient
 *              from signed (-3328 .. 3328) form to
 *              unsigned form (0 .. 3328).
 *
 * Note: Cryptographic constant time implementation
 *
 * Examples:       0 -> 0
 *                 1 -> 1
 *              3328 -> 3328
 *                -1 -> 3328
 *                -2 -> 3327
 *             -3328 -> 1
 *
 * Arguments: c: signed coefficient to be converted
 ************************************************************/
STATIC_INLINE_TESTABLE
uint16_t scalar_signed_to_unsigned_q(int16_t c)  // clang-format off
  REQUIRES(c >= -(MLKEM_Q - 1) && c <= (MLKEM_Q - 1))
  ENSURES(RETURN_VALUE >= 0 && RETURN_VALUE <= (MLKEM_Q - 1))
  ENSURES(RETURN_VALUE == (int32_t)c + (((int32_t)c < 0) * MLKEM_Q))
{  // clang-format on
  // Add Q if c is negative, but in constant time
  cmov_int16(&c, c + MLKEM_Q, c < 0);

  ASSERT(c >= 0, "scalar_signed_to_unsigned_q result lower bound");
  ASSERT(c < MLKEM_Q, "scalar_signed_to_unsigned_q result upper bound");

  // and therefore cast to uint16_t is safe.
  return (uint16_t)c;
}

#define poly_compress MLKEM_NAMESPACE(poly_compress)
/*************************************************
 * Name:        poly_compress
 *
 * Description: Compression and subsequent serialization of a polynomial
 *
 * Arguments:   - uint8_t *r: pointer to output byte array
 *                            (of length MLKEM_POLYCOMPRESSEDBYTES)
 *              - const poly *a: pointer to input polynomial
 *                  Coefficients must be unsigned canonical,
 *                  i.e. in [0,1,..,MLKEM_Q-1].
 **************************************************/
void poly_compress(uint8_t r[MLKEM_POLYCOMPRESSEDBYTES], const poly *a)
    // clang-format off
REQUIRES(IS_FRESH(r, MLKEM_POLYCOMPRESSEDBYTES))
REQUIRES(IS_FRESH(a, sizeof(poly)))
REQUIRES(ARRAY_IN_BOUNDS(int, k, 0, (MLKEM_N - 1), a->coeffs, 0, (MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(r));
// clang-format on

#define poly_decompress MLKEM_NAMESPACE(poly_decompress)
/*************************************************
 * Name:        poly_decompress
 *
 * Description: De-serialization and subsequent decompression of a polynomial;
 *              approximate inverse of poly_compress
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *a: pointer to input byte array
 *                                  (of length MLKEM_POLYCOMPRESSEDBYTES bytes)
 *
 * Upon return, the coefficients of the output polynomial are unsigned-canonical
 * (non-negative and smaller than MLKEM_Q).
 *
 **************************************************/
void poly_decompress(poly *r, const uint8_t a[MLKEM_POLYCOMPRESSEDBYTES])
    // clang-format off
REQUIRES(IS_FRESH(a, MLKEM_POLYCOMPRESSEDBYTES))
REQUIRES(IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_WHOLE(r))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, (MLKEM_N - 1), r->coeffs, 0, (MLKEM_Q - 1)));
// clang-format on

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
void poly_tobytes(uint8_t r[MLKEM_POLYBYTES], const poly *a)
    // clang-format off
REQUIRES(IS_FRESH(r, MLKEM_POLYBYTES))
REQUIRES(IS_FRESH(a, sizeof(poly)))
REQUIRES(ARRAY_IN_BOUNDS(int, k, 0, (MLKEM_N - 1), a->coeffs, 0, (MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(r));
// clang-format on


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
void poly_frombytes(poly *r, const uint8_t a[MLKEM_POLYBYTES])
    // clang-format off
REQUIRES(IS_FRESH(a, MLKEM_POLYBYTES))
REQUIRES(IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, (MLKEM_N - 1), r->coeffs, 0, 4095));
// clang-format on


#define poly_frommsg MLKEM_NAMESPACE(poly_frommsg)
/*************************************************
 * Name:        poly_frommsg
 *
 * Description: Convert 32-byte message to polynomial
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *msg: pointer to input message
 **************************************************/
void poly_frommsg(poly *r, const uint8_t msg[MLKEM_INDCPA_MSGBYTES])
    // clang-format off
REQUIRES(IS_FRESH(msg, MLKEM_INDCPA_MSGBYTES))
REQUIRES(IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_WHOLE(r))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, (MLKEM_N - 1), r->coeffs, 0, (MLKEM_Q - 1)));
// clang-format on


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
void poly_tomsg(uint8_t msg[MLKEM_INDCPA_MSGBYTES], const poly *r)
    // clang-format off
REQUIRES(IS_FRESH(msg, MLKEM_INDCPA_MSGBYTES))
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(ARRAY_IN_BOUNDS(int, k, 0, (MLKEM_N - 1), r->coeffs, 0, (MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(msg));
// clang-format on



#define poly_getnoise_eta1_4x MLKEM_NAMESPACE(poly_getnoise_eta1_4x)
/*************************************************
 * Name:        poly_getnoise_eta1_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed
 * and nonces, with output polynomials close to centered binomial distribution
 * with parameter MLKEM_ETA1.
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length MLKEM_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta1_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                           const uint8_t seed[MLKEM_SYMBYTES], uint8_t nonce0,
                           uint8_t nonce1, uint8_t nonce2,
                           uint8_t nonce3)  // clang-format off
REQUIRES(IS_FRESH(r0, sizeof(poly)))
REQUIRES(IS_FRESH(r1, sizeof(poly)))
REQUIRES(IS_FRESH(r2, sizeof(poly)))
REQUIRES(IS_FRESH(r3, sizeof(poly)))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(r0), OBJECT_WHOLE(r1), OBJECT_WHOLE(r2), OBJECT_WHOLE(r3))
ENSURES(                                                                          \
    ARRAY_IN_BOUNDS(int, k0, 0, MLKEM_N - 1, r0->coeffs, -MLKEM_ETA1, MLKEM_ETA1) \
 && ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, r1->coeffs, -MLKEM_ETA1, MLKEM_ETA1) \
 && ARRAY_IN_BOUNDS(int, k2, 0, MLKEM_N - 1, r2->coeffs, -MLKEM_ETA1, MLKEM_ETA1) \
 && ARRAY_IN_BOUNDS(int, k3, 0, MLKEM_N - 1, r3->coeffs, -MLKEM_ETA1, MLKEM_ETA1));
// clang-format on

#define poly_getnoise_eta2 MLKEM_NAMESPACE(poly_getnoise_eta2)
/*************************************************
 * Name:        poly_getnoise_eta2
 *
 * Description: Sample a polynomial deterministically from a seed and a nonce,
 *              with output polynomial close to centered binomial distribution
 *              with parameter MLKEM_ETA2
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length MLKEM_SYMBYTES bytes)
 *              - uint8_t nonce: one-byte input nonce
 **************************************************/
void poly_getnoise_eta2(poly *r, const uint8_t seed[MLKEM_SYMBYTES],
                        uint8_t nonce)  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(r))
ENSURES(ARRAY_IN_BOUNDS(int, k0, 0, MLKEM_N - 1, r->coeffs, -MLKEM_ETA2, MLKEM_ETA2));
// clang-format on

#define poly_getnoise_eta2_4x MLKEM_NAMESPACE(poly_getnoise_eta2_4x)
/*************************************************
 * Name:        poly_getnoise_eta2_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed
 * and nonces, with output polynomials close to centered binomial distribution
 * with parameter MLKEM_ETA2
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length MLKEM_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta2_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                           const uint8_t seed[MLKEM_SYMBYTES], uint8_t nonce0,
                           uint8_t nonce1, uint8_t nonce2,
                           uint8_t nonce3)  // clang-format off
REQUIRES(IS_FRESH(r0, sizeof(poly)))
REQUIRES(IS_FRESH(r1, sizeof(poly)))
REQUIRES(IS_FRESH(r2, sizeof(poly)))
REQUIRES(IS_FRESH(r3, sizeof(poly)))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(r0), OBJECT_WHOLE(r1), OBJECT_WHOLE(r2), OBJECT_WHOLE(r3))
ENSURES(                                                                          \
    ARRAY_IN_BOUNDS(int, k0, 0, MLKEM_N - 1, r0->coeffs, -MLKEM_ETA2, MLKEM_ETA2) \
 && ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, r1->coeffs, -MLKEM_ETA2, MLKEM_ETA2) \
 && ARRAY_IN_BOUNDS(int, k2, 0, MLKEM_N - 1, r2->coeffs, -MLKEM_ETA2, MLKEM_ETA2) \
 && ARRAY_IN_BOUNDS(int, k3, 0, MLKEM_N - 1, r3->coeffs, -MLKEM_ETA2, MLKEM_ETA2));
// clang-format on

#define poly_getnoise_eta1122_4x MLKEM_NAMESPACE(poly_getnoise_eta1122_4x)
/*************************************************
 * Name:        poly_getnoise_eta1122_4x
 *
 * Description: Batch sample four polynomials deterministically from a seed
 * and a nonces, with output polynomials close to centered binomial
 * distribution with parameter MLKEM_ETA1 and MLKEM_ETA2
 *
 * Arguments:   - poly *r{0,1,2,3}: pointer to output polynomial
 *              - const uint8_t *seed: pointer to input seed
 *                                     (of length MLKEM_SYMBYTES bytes)
 *              - uint8_t nonce{0,1,2,3}: one-byte input nonce
 **************************************************/
void poly_getnoise_eta1122_4x(poly *r0, poly *r1, poly *r2, poly *r3,
                              const uint8_t seed[MLKEM_SYMBYTES],
                              uint8_t nonce0, uint8_t nonce1, uint8_t nonce2,
                              uint8_t nonce3)  // clang-format off
REQUIRES(IS_FRESH(r0, sizeof(poly)))
REQUIRES(IS_FRESH(r1, sizeof(poly)))
REQUIRES(IS_FRESH(r2, sizeof(poly)))
REQUIRES(IS_FRESH(r3, sizeof(poly)))
REQUIRES(IS_FRESH(seed, MLKEM_SYMBYTES))
ASSIGNS(OBJECT_WHOLE(r0), OBJECT_WHOLE(r1), OBJECT_WHOLE(r2), OBJECT_WHOLE(r3))
ENSURES(                                                                          \
    ARRAY_IN_BOUNDS(int, k0, 0, MLKEM_N - 1, r0->coeffs, -MLKEM_ETA1, MLKEM_ETA1) \
 && ARRAY_IN_BOUNDS(int, k1, 0, MLKEM_N - 1, r1->coeffs, -MLKEM_ETA1, MLKEM_ETA1) \
 && ARRAY_IN_BOUNDS(int, k2, 0, MLKEM_N - 1, r2->coeffs, -MLKEM_ETA2, MLKEM_ETA2) \
 && ARRAY_IN_BOUNDS(int, k3, 0, MLKEM_N - 1, r3->coeffs, -MLKEM_ETA2, MLKEM_ETA2));
// clang-format on

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
 *              The result is coefficient-wise bound by 3/2 q in absolute
 *              value.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const poly *a: pointer to first input polynomial
 *              - const poly *b: pointer to second input polynomial
 *              - const poly_mulcache *b_cache: pointer to mulcache
 *                  for second input polynomial. Can be computed
 *                  via poly_mulcache_compute().
 **************************************************/
void poly_basemul_montgomery_cached(poly *r, const poly *a, const poly *b,
                                    const poly_mulcache *b_cache)
    // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(a, sizeof(poly)))
REQUIRES(IS_FRESH(b, sizeof(poly)))
REQUIRES(IS_FRESH(b_cache, sizeof(poly_mulcache)))
REQUIRES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, a->coeffs, -(MLKEM_Q - 1), (MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(r))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs, -3 * HALF_Q + 1, 3 * HALF_Q - 1));
// clang-format on

// clang-format off
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
void poly_tomont(poly *r)
REQUIRES(IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs, -(MLKEM_Q - 1), (MLKEM_Q - 1)));
// clang-format on

// REF-CHANGE: This function does not exist in the reference implementation
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
// NOTE: The default C implementation of this function populates
// the mulcache with values in (-q,q), but this is not needed for the
// higher level safety proofs, and thus not part of the spec.
void poly_mulcache_compute(poly_mulcache *x, const poly *a)
    // clang-format off
REQUIRES(IS_FRESH(x, sizeof(poly_mulcache)))
REQUIRES(IS_FRESH(a, sizeof(poly)))
ASSIGNS(OBJECT_WHOLE(x));
// clang-format on

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
// REF-CHANGE: The semantics of poly_reduce() is different in
//             the reference implementation, which requires
//             signed canonical output data. Unsigned canonical
//             outputs are better suited to the only remaining
//             use of poly_reduce() in the context of (de)serialization.
void poly_reduce(poly *r)
    // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs, 0, MLKEM_Q - 1));
// clang-format on

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
// REF-CHANGE:
// The reference implementation uses a 3-argument poly_add.
// We specialize to the accumulator form to avoid reasoning about aliasing.
void poly_add(poly *r, const poly *b)  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(b, sizeof(poly)))
REQUIRES(FORALL(int, k0, 0, MLKEM_N - 1, (int32_t) r->coeffs[k0] + b->coeffs[k0] <= INT16_MAX))
REQUIRES(FORALL(int, k1, 0, MLKEM_N - 1, (int32_t) r->coeffs[k1] + b->coeffs[k1] >= INT16_MIN))
ENSURES(FORALL(int, k, 0, MLKEM_N - 1, r->coeffs[k] == OLD(*r).coeffs[k] + b->coeffs[k]))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)));
// clang-format on

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
// REF-CHANGE:
// The reference implementation uses a 3-argument poly_sub.
// We specialize to the accumulator form to avoid reasoning about aliasing.
void poly_sub(poly *r, const poly *b)  // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(b, sizeof(poly)))
REQUIRES(FORALL(int, k0, 0, MLKEM_N - 1, (int32_t) r->coeffs[k0] - b->coeffs[k0] <= INT16_MAX))
REQUIRES(FORALL(int, k1, 0, MLKEM_N - 1, (int32_t) r->coeffs[k1] - b->coeffs[k1] >= INT16_MIN))
ENSURES(FORALL(int, k, 0, MLKEM_N - 1, r->coeffs[k] == OLD(*r).coeffs[k] - b->coeffs[k]))
ASSIGNS(OBJECT_WHOLE(r));
// clang-format on

#endif
