// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"


unsigned mlk_rej_uniform(int16_t *r, unsigned target, unsigned offset,
                         const uint8_t *buf, unsigned buflen);

void harness(void)
{
  unsigned target, offset, inlen;
  int16_t *r;
  uint8_t *buf;

  mlk_rej_uniform(r, target, offset, buf, inlen);
}
