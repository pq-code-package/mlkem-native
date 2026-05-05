// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <keccakf1600.h>


void mlk_keccakf1600x4_xor_bytes_c(uint64_t *state, const unsigned char *data0,
                                   const unsigned char *data1,
                                   const unsigned char *data2,
                                   const unsigned char *data3, unsigned offset,
                                   unsigned length);

void harness(void)
{
  uint64_t *state;
  const unsigned char *data0, *data1, *data2, *data3;
  unsigned offset;
  unsigned length;
  mlk_keccakf1600x4_xor_bytes_c(state, data0, data1, data2, data3, offset,
                                length);
}
