// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "sampling.h"

void harness(void)
{
  mlk_poly *out0;
  mlk_poly *out1;
  mlk_poly *out2;
  mlk_poly *out3;
  uint8_t(*seed)[MLK_ALIGN_UP(MLKEM_SYMBYTES + 2)];
  mlk_poly_rej_uniform_x4(out0, out1, out2, out3, seed);
}
