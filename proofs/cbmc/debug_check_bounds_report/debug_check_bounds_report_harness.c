// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "debug.h"

int mlk_debug_check_bounds_report(const char *file, size_t file_len, int line,
                                  const int16_t *ptr, unsigned len,
                                  int lower_bound_exclusive,
                                  int upper_bound_exclusive);

void harness(void)
{
  const char *file;
  size_t file_len;
  int line;
  const int16_t *ptr;
  unsigned len;
  int lower_bound_exclusive;
  int upper_bound_exclusive;

  mlk_debug_check_bounds_report(file, file_len, line, ptr, len,
                                lower_bound_exclusive, upper_bound_exclusive);
}
