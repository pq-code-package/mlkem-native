// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "common.h"

#define ntt_butterfly_block MLKEM_NAMESPACE(ntt_butterfly_block)
void ntt_butterfly_block(int16_t *r, int16_t root, unsigned start, unsigned len,
                         int bound);

void harness(void)
{
  int16_t *r, root;
  unsigned start, stride;
  int bound;
  ntt_butterfly_block(r, root, start, stride, bound);
}
