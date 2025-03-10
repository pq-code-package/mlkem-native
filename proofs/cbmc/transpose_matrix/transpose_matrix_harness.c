// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

void mlk_transpose_matrix(mlk_polyvec a[MLKEM_K]);
void harness(void)
{
  mlk_polyvec *a;
  mlk_transpose_matrix(a);
}
