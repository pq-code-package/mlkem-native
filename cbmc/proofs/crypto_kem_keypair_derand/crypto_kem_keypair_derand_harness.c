// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file crypto_kem_keypair_derand_harness.c
 * @brief Implements the proof harness for crypto_kem_keypair_derand function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <kem.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  uint8_t *a, *b, *c;
  crypto_kem_keypair_derand(a, b, c);
}
