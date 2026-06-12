// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "common.h"


void mlk_ntt_2_layers_block(int16_t *r, unsigned start, unsigned len,
                            int16_t z0, int16_t z0_twst, int16_t z1,
                            int16_t z1_twst, int16_t z2, int16_t z2_twst,
                            const int16_t bound);

void harness(void)
{
  int16_t *r;
  unsigned start, len;
  int16_t z0, z0_twst, z1, z1_twst, z2, z2_twst, bound;
  mlk_ntt_2_layers_block(r, start, len, z0, z0_twst, z1, z1_twst, z2, z2_twst,
                         bound);
}
