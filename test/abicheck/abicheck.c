/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>
#include "abicheck_common.h"
#if defined(MLK_SYS_AARCH64)
#include "aarch64/checks_aarch64_all.h"
#elif defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)
#include "x86_64/checks_x86_64_all.h"
#elif defined(MLK_SYS_PPC64LE)
#include "ppc64le/checks_ppc64le_all.h"
#elif defined(MLK_SYS_ARMV81M_MVE)
#include "armv81m/checks_armv81m_all.h"
#else
/* No abicheck support on this architecture - empty registry, driver runs zero
 * kernel checks (selftest still runs). */
static const abicheck_entry_t all_checks[] = {{NULL, NULL}};
#endif
#include "selftest.h"

/* Return-code convention: see abicheck_common.h. SKIPPED means the kernel
 * built but the host lacks the runtime capability; the generated check
 * decides this via mlk_sys_check_capability. */
int main(void)
{
  int failed_tests = 0;
  int selftest_failures;
  const abicheck_entry_t *entry;

  /* Meta-test the ABI checker before trusting kernel verdicts (see selftest.h).
   */
  selftest_failures = abicheck_selftest();
  if (selftest_failures > 0)
  {
    fprintf(stderr, "abicheck selftest FAILED (%d failure(s)); aborting.\n",
            selftest_failures);
    return 1;
  }
  printf("ABI checker selftest... PASSED\n");

  /* all_checks comes from checks_<arch>_all.h (sentinel-only on unsupported
   * archs, in which case this loop is a no-op). */
  for (entry = all_checks; entry->name != NULL; entry++)
  {
    int rc = entry->check_func();
    if (rc == MLK_ABICHECK_PASSED)
    {
      printf("ABI check for %s... PASSED\n", entry->name);
    }
    else if (rc == MLK_ABICHECK_SKIPPED)
    {
      printf("ABI check for %s... SKIPPED\n", entry->name);
    }
    else
    {
      printf("ABI check for %s... FAILED\n", entry->name);
      failed_tests++;
    }
  }

  if (failed_tests > 0)
  {
    return 1;
  }
  return 0;
}
