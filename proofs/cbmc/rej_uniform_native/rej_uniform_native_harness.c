// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"

#define rej_uniform MLKEM_NAMESPACE(rej_uniform)
unsigned int rej_uniform(int16_t *r, unsigned int target, unsigned int offset,
                         const uint8_t *buf, unsigned int buflen);

void harness(void)
{
  unsigned int target, offset, inlen;
  int16_t *r;
  uint8_t *buf;

  rej_uniform(r, target, offset, buf, inlen);
}
