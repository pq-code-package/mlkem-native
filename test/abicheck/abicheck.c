/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include <stdlib.h>
#include "../../mlkem/src/sys.h"
#include "checks_all.h"

int main(void)
{
#ifdef MLK_SYS_AARCH64
  int total_tests = 0;
  int failed_tests = 0;

  printf("Running ABI compliance tests for all functions\n");
  printf("==============================================\n");

  for (const abicheck_entry_t *entry = all_checks; entry->name != NULL; entry++)
  {
    printf("* %s... ", entry->name);
    total_tests++;

    if (entry->check_func() != 0)
    {
      printf("FAILED!\n");
      failed_tests++;
    }
    else
    {
      printf("PASSED\n");
    }
  }

  printf("==============================================\n");
  printf("ABI Test Summary: %d/%d tests passed\n", total_tests - failed_tests,
         total_tests);

  if (failed_tests > 0)
  {
    printf("OVERALL RESULT: FAILED (%d failures)\n", failed_tests);
    return 1;
  }
  else
  {
    printf("OVERALL RESULT: PASSED\n");
    return 0;
  }
#else  /* MLK_SYS_AARCH64 */
  printf(
      "ABI check is not yet implemented for architectures other than "
      "AArch64\n");
  printf("Skipping ABI check...\n");
  return 0;
#endif /* !MLK_SYS_AARCH64 */
}
