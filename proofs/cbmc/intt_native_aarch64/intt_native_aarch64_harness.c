// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

int mlk_intt_native(int16_t data[MLKEM_N]);

void harness(void)
{
  int16_t *r;
  int t;
  t = mlk_intt_native(r);
}
