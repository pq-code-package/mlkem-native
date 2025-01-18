/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef CBD_H
#define CBD_H

#include <stdint.h>
#include "common.h"
#include "poly.h"

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

#if MLKEM_ETA1 == 3
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
#endif /* MLKEM_ETA1 == 3 */

#define poly_cbd_eta1 MLKEM_NAMESPACE(poly_cbd_eta1)
/*************************************************
 * Name:        poly_cbd_eta1
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter MLKEM_ETA1.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
static INLINE void poly_cbd_eta1(poly *r,
                                 const uint8_t buf[MLKEM_ETA1 * MLKEM_N / 4])
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(buf, MLKEM_ETA1 * MLKEM_N / 4))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_ETA1 + 1))
)
{
#if MLKEM_ETA1 == 2
  poly_cbd2(r, buf);
#elif MLKEM_ETA1 == 3
  poly_cbd3(r, buf);
#else
#error "Invalid value of MLKEM_ETA1"
#endif
}

#if MLKEM_K == 2 || MLKEM_K == 4
#define poly_cbd_eta2 MLKEM_NAMESPACE(poly_cbd_eta2)
/*************************************************
 * Name:        poly_cbd_eta1
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter MLKEM_ETA2.
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
static INLINE void poly_cbd_eta2(poly *r,
                                 const uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4])
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(memory_no_alias(buf, MLKEM_ETA2 * MLKEM_N / 4))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_ETA2 + 1)))
{
#if MLKEM_ETA2 == 2
  poly_cbd2(r, buf);
#else
#error "Invalid value of MLKEM_ETA2"
#endif
}
#endif /* MLKEM_K == 2 || MLKEM_K == 4 */

#endif
