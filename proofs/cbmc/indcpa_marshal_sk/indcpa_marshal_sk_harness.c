// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

void harness(void)
{
  uint8_t *sk;
  mlk_indcpa_secret_key *sks;
  mlk_indcpa_marshal_sk(sk, sks);
}
