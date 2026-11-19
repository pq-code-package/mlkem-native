// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>


void mlk_keccak_squeeze_once(uint8_t *h, size_t outlen, uint64_t *s,
                             unsigned r);

void harness(void)
{
  uint8_t *h;
  size_t outlen;
  uint64_t *s;
  unsigned r;
  mlk_keccak_squeeze_once(h, outlen, s, r);
}
