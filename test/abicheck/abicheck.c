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
  int result;
  int failed_tests = 0;
  const abicheck_entry_t *entry;

  for (entry = all_checks; entry->name != NULL; entry++)
  {
    printf("Running ABI check for %s... ", entry->name);
    fflush(stdout);

    result = entry->check_func();
    if (result != 0)
    {
      printf("FAILED\n");
      failed_tests++;
    }
    else
    {
      printf("PASSED\n");
    }
  }

  if (failed_tests > 0)
  {
    return 1;
  }
  else
  {
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
