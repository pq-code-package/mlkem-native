// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define keccak_squeezeblocks MLKEM_NAMESPACE(keccak_squeezeblocks)
void keccak_squeezeblocks(uint8_t *h, size_t nblocks, uint64_t *s, uint32_t r);

void harness(void)
{
  uint8_t *h;
  size_t nblocks;
  uint64_t *s;
  uint32_t r;
  keccak_squeezeblocks(h, nblocks, s, r);
}
