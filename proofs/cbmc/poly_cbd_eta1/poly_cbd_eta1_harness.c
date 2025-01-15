// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <cbd.h>

void harness(void)
{
  uint8_t *buf;
  poly *a;

  poly_cbd_eta1(a, buf);
}
