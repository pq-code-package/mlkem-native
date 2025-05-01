// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "poly.h"

#define mlk_poly_cbd_eta1 MLK_NAMESPACE(poly_cbd_eta1)
void mlk_poly_cbd_eta1(mlk_poly *r,
                       const uint8_t buf[MLKEM_ETA1 * MLKEM_N / 4]);

void harness(void)
{
  uint8_t *buf;
  mlk_poly *a;

  mlk_poly_cbd_eta1(a, buf);
}
