// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "sampling.h"

void harness(void)
{
  int16_t *r;
  unsigned target, offset;
  uint8_t *buf;
  unsigned buflen;

  mlk_rej_uniform_c(r, target, offset, buf, buflen);
}
