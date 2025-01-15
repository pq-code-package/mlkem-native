// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include "cbmc.h"
#include "rej_uniform.h"

void harness(void)
{
  unsigned int target, offset, inlen;
  int16_t *r;
  uint8_t *buf;

  rej_uniform(r, target, offset, buf, inlen);
}
