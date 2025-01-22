// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

void mlk_ntt_layer7(int16_t *r);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  int16_t *a;
  mlk_ntt_layer7(a);
}
