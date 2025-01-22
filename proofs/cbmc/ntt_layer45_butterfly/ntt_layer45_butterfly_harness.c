// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

#define ntt_layer45_butterfly MLK_NAMESPACE(ntt_layer45_butterfly)
void ntt_layer45_butterfly(int16_t r[MLKEM_N],
                           const unsigned zeta_subtree_index,
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
  ntt_layer45_butterfly(a, zi, start);
}
