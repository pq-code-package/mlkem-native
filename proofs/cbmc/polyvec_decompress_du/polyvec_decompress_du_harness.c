// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "poly.h"
#include "polyvec.h"

void harness(void)
{
  polyvec *a;
  uint8_t *r;

  polyvec_decompress_du(a, r);
}
