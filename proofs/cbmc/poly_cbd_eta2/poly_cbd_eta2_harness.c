// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "poly.h"

#define poly_cbd_eta2 MLKEM_NAMESPACE(poly_cbd_eta2)
void poly_cbd_eta2(poly *r, const uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4]);

void harness(void)
{
  /* poly_cbd_eta2() is only defined for MLKEM_K == 2 or 4 */
#if MLKEM_K == 2 || MLKEM_K == 4
  uint8_t *buf;
  poly *a;

  poly_cbd_eta2(a, buf);
#endif /* MLKEM_K == 2 || MLKEM_K == 4 */
}
