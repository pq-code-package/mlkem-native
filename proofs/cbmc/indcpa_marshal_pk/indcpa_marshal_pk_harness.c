// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

void harness(void)
{
  uint8_t *pk;
  mlk_indcpa_public_key *pks;
  mlk_indcpa_marshal_pk(pk, pks);
}
