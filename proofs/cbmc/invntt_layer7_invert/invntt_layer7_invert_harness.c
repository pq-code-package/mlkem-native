// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <poly.h>

#define invntt_layer7_invert MLK_NAMESPACE(invntt_layer7_invert)
void invntt_layer7_invert(int16_t *r);

/**
 * @brief Starting point for formal analysis
 *
 */
void harness(void)
{
  int16_t *a;
  invntt_layer7_invert(a);
}
