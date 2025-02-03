// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "poly.h"

#define poly_cbd_eta1 MLKEM_NAMESPACE(poly_cbd_eta1)
void poly_cbd_eta1(poly *r, const uint8_t buf[MLKEM_ETA1 * MLKEM_N / 4]);

void harness(void)
{
  uint8_t *buf;
  poly *a;

  poly_cbd_eta1(a, buf);
}
