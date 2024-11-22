// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file polyvec_tobytes_harness.c
 * @brief Implements the proof harness for polyvec_tobytes function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <polyvec.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  polyvec *a;
  uint8_t *r;
  polyvec_tobytes(r, a);
}
