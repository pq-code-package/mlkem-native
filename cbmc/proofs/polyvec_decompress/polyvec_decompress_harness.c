// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file polyvec_decompress_harness.c
 * @brief Implements the proof harness for polyvec_decompress function.
 */
#include "poly.h"
#include "polyvec.h"

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *a;
  uint8_t *r;

  // TODO: remove cbmc-viewer.json
  // TODO: remove the README for all proofs

  polyvec_decompress(a, r);
}
