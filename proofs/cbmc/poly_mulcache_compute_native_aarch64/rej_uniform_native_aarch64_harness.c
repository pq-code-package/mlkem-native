// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "cbmc.h"


int mlk_rej_uniform_native(int16_t *r, unsigned len, const uint8_t *buf,
                           unsigned buflen);

void harness(void)
{
  int16_t *r;
  unsigned len;
  const uint8_t *buf;
  unsigned buflen;

  mlk_rej_uniform_native(r, len, buf, buflen);
}
