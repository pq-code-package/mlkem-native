// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "poly.h"


void mlk_ntt_layer(int16_t *p, unsigned layer);

void harness(void)
{
  int16_t *a;
  unsigned layer;
  mlk_ntt_layer(a, layer);
}
