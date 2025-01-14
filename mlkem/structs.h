/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef STRUCTS_H
#define STRUCTS_H

#include <stdint.h>
#include "common.h"

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

#define polyvec MLKEM_NAMESPACE(polyvec)
typedef struct
{
  poly vec[MLKEM_K];
} ALIGN polyvec;

#define polyvec_mulcache MLKEM_NAMESPACE(polyvec_mulcache)
typedef struct
{
  poly_mulcache vec[MLKEM_K];
} polyvec_mulcache;

#endif
