// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <kem.h>

void harness(void)
{
  mlk_secret_key *sk;
  mlk_public_key *pk;
  mlk_pk_from_sk(pk, sk);
}
