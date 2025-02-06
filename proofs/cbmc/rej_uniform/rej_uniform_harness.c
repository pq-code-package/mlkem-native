// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"

#define rej_uniform MLK_NAMESPACE(rej_uniform)
unsigned rej_uniform(int16_t *r, unsigned target, unsigned offset,
                     const uint8_t *buf, unsigned buflen);

void harness(void)
{
  unsigned target, offset, inlen;
  int16_t *r;
  uint8_t *buf;

  rej_uniform(r, target, offset, buf, inlen);
}
