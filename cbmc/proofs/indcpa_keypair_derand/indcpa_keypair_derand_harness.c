// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file indcpa_keypair_derand_harness.c
 * @brief Implements the proof harness for indcpa_keypair_derand function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <indcpa.h>

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void) {
  uint8_t *a, *b, *c;
  indcpa_keypair_derand(a, b, c);
}
