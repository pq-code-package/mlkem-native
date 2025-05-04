// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

void mlk_transpose_matrix(mlk_polymat a);
void harness(void)
{
  mlk_polymat a;
  mlk_transpose_matrix(a);
}
