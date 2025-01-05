// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define keccak_absorb_once FIPS202_NAMESPACE(keccak_absorb_once)
void keccak_absorb_once(uint64_t *s, uint32_t r, const uint8_t *m, size_t mlen,
                        uint8_t p);

void harness(void)
{
  uint64_t *s;
  uint32_t r;
  const uint8_t *m;
  size_t mlen;
  uint8_t p;
  keccak_absorb_once(s, r, m, mlen, p);
}
