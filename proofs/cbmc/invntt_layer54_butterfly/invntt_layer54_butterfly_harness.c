// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <ntt.h>

#define invntt_layer54_butterfly MLKEM_NAMESPACE(invntt_layer54_butterfly)
void invntt_layer54_butterfly(int16_t r[MLKEM_N], const unsigned zeta_index,
                              const unsigned start);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  int16_t *a;
  unsigned zi;
  unsigned start;
  invntt_layer54_butterfly(a, zi, start);
}
