/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include "checks_all.h"

int main(void)
{
  int failed_tests = 0;
  const abicheck_entry_t *entry;

  /* all_checks is generated in checks_all.h. On architectures the ABI checker
   * does not support it is an empty (sentinel-only) array, so this loop runs
   * zero checks and the program exits successfully. */
  for (entry = all_checks; entry->name != NULL; entry++)
  {
    if (entry->check_func() != 0)
    {
      printf("ABI check for %s... FAILED\n", entry->name);
      failed_tests++;
    }
    else
    {
      printf("ABI check for %s... PASSED\n", entry->name);
    }
  }

  if (failed_tests > 0)
  {
    return 1;
  }
  return 0;
}
