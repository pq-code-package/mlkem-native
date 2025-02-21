// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define mlk_keccak_absorb_once MLK_NAMESPACE(keccak_absorb_once)
void mlk_keccak_absorb_once(uint64_t *s, uint32_t r, const uint8_t *m,
                            size_t mlen, uint8_t p);

void harness(void)
{
  uint64_t *s;
  uint32_t r;
  const uint8_t *m;
  size_t mlen;
  uint8_t p;
  mlk_keccak_absorb_once(s, r, m, mlen, p);
}
