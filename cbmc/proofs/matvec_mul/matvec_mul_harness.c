// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file matvec_mul_harness.c
 * @brief Implements the proof harness for poly_reduce function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "indcpa.h"
#include "polyvec.h"

void matvec_mul(polyvec *out, polyvec const *a, polyvec const *v,
                polyvec_mulcache const *vc);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *out, *a, *v;
  polyvec_mulcache *vc;
  matvec_mul(out, a, v, vc);
}
