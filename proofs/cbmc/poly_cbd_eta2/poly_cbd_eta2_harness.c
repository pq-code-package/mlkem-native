// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <cbd.h>

void harness(void)
{
  /* poly_cbd_eta2() is only defined for MLKEM_K == 2 or 4 */
#if MLKEM_K == 2 || MLKEM_K == 4
  uint8_t *buf;
  poly *a;

  poly_cbd_eta2(a, buf);
#endif /* MLKEM_K == 2 || MLKEM_K == 4 */
}
