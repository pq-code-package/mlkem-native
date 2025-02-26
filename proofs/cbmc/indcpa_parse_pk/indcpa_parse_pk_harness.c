// Copyright (c) 2024-2025 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <indcpa.h>

void harness(void)
{
  uint8_t *pk;
  mlk_indcpa_public_key *pks;
  mlk_indcpa_parse_pk(pks, pk);
}
