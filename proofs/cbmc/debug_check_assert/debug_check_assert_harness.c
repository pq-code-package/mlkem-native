// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "debug.h"

void harness(void)
{
  const char *file;
  size_t file_len;
  int line;
  int val;

  mlk_debug_check_assert(file, file_len, line, val);
}
