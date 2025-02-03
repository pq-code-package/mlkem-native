// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "poly.h"

#define ntt_layer MLKEM_NAMESPACE(ntt_layer)
void ntt_layer(int16_t *p, unsigned len, unsigned layer);

void harness(void)
{
  int16_t *a;
  unsigned len, layer;
  ntt_layer(a, len, layer);
}
