// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

/*
 * Insert copyright notice
 */

/**
 * @file ntt_layer7_butterfly_harness.c
 * @brief Implements the proof harness for ntt_layer7_butterfly function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include <ntt.h>
void ntt_layer7_butterfly(int16_t *r, int zetaindex, int start);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  int16_t *a;
  int zi;
  int start;
  ntt_layer7_butterfly(a, zi, start);
}
