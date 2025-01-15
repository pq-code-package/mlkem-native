// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "common.h"

#define invntt_layer MLKEM_NAMESPACE(invntt_layer)
void invntt_layer(int16_t *p, unsigned len, unsigned layer);

void harness(void)
{
  int16_t *a;
  unsigned len, layer;
  invntt_layer(a, len, layer);
}
