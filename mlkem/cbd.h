// SPDX-License-Identifier: Apache-2.0
#ifndef CBD_H
#define CBD_H

#include <stdint.h>
#include "params.h"
#include "poly.h"

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
void poly_cbd_eta1(poly *r, const uint8_t buf[MLKEM_ETA1 * MLKEM_N / 4])
    // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(buf, MLKEM_ETA1 * MLKEM_N / 4))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs, -MLKEM_ETA1, MLKEM_ETA1));
// clang-format on

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
void poly_cbd_eta2(poly *r, const uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4])
    // clang-format off
REQUIRES(IS_FRESH(r, sizeof(poly)))
REQUIRES(IS_FRESH(buf, MLKEM_ETA2 * MLKEM_N / 4))
ASSIGNS(OBJECT_UPTO(r, sizeof(poly)))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs, -MLKEM_ETA2, MLKEM_ETA2));
// clang-format on

#endif
