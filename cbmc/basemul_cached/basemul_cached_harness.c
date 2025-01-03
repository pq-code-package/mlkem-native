// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0


#include "ntt.h"
#include "reduce.h"

void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                    const int16_t b_cached);

void harness(void)
{
  int16_t *a, *b, *r, b_cached;

  basemul_cached(r, a, b, b_cached);
}
