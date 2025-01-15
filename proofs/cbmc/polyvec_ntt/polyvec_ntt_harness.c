// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "ntt.h"
#include "polyvec.h"

void harness(void)
{
  polyvec *r;
  polyvec_ntt(r);
}
