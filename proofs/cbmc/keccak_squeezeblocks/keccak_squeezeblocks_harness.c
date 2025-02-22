// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define mlk_keccak_squeezeblocks MLK_NAMESPACE(keccak_squeezeblocks)
void mlk_keccak_squeezeblocks(uint8_t *h, size_t nblocks, uint64_t *s,
                              uint32_t r);

void harness(void)
{
  uint8_t *h;
  size_t nblocks;
  uint64_t *s;
  uint32_t r;
  mlk_keccak_squeezeblocks(h, nblocks, s, r);
}
