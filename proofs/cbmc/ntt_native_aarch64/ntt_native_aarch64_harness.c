// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

void mlk_ntt_native(int16_t data[MLKEM_N]);

void harness(void)
{
  int16_t *r;
  mlk_ntt_native(r);
}
