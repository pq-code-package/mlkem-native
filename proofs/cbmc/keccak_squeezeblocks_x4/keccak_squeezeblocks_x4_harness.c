// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define keccak_squeezeblocks_x4 MLKEM_NAMESPACE(keccak_squeezeblocks_x4)
void keccak_squeezeblocks_x4(uint8_t *out0, uint8_t *out1, uint8_t *out2,
                             uint8_t *out3, size_t nblocks, uint64_t *s,
                             uint32_t r);

void harness(void)
{
  uint8_t *out0, out1, out2, out3;
  size_t nblocks;
  uint64_t *s;
  uint32_t r;
  keccak_squeezeblocks_x4(out0, out1, out2, out3, nblocks, s, r);
}
