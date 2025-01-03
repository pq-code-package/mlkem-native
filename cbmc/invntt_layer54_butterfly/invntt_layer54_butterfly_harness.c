// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <ntt.h>
void invntt_layer54_butterfly(int16_t *r, int zeta_index, int start);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  int16_t *a;
  int zi;
  int start;
  invntt_layer54_butterfly(a, zi, start);
}
