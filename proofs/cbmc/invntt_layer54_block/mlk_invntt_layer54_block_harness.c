// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

void mlk_invntt_layer54_block(int16_t r[MLKEM_N], const unsigned zeta_index,
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
  mlk_invntt_layer54_block(a, zi, start);
}
