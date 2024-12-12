// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
void invntt_layer(int16_t *p, int len, int layer);

void harness(void)
{
  int16_t *a;
  int len, layer;
  invntt_layer(a, len, layer);
}
