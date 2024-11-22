// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

/*
 * Insert copyright notice
 */

/**
 * @file polyvec_mulcache_compute_harness.c
 * @brief Implements the proof harness for polyvec_mulcache_compute function.
 */
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
  polyvec_mulcache *x;
  polyvec *a;

  polyvec_mulcache_compute(x, a);
}
