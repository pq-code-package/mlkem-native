// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "poly.h"

#define mlk_poly_cbd_eta2 MLK_NAMESPACE(poly_cbd_eta2)
void mlk_poly_cbd_eta2(mlk_poly *r,
                       const uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4]);

void harness(void)
{
  /* mlk_poly_cbd_eta2() is only defined for MLKEM_K == 2 or 4 */
#if MLKEM_K == 2 || MLKEM_K == 4
  uint8_t *buf;
  mlk_poly *a;

  mlk_poly_cbd_eta2(a, buf);
#endif /* MLKEM_K == 2 || MLKEM_K == 4 */
}
