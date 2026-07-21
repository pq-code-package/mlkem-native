/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [AAPCS64]
 *   Procedure Call Standard for the Arm 64-bit Architecture (AAPCS64)
 *   Arm Limited
 *   https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst
 */

#include <stdio.h>

#include "../../notrandombytes/notrandombytes.h"
#include "abicheck_aarch64.h"

#if defined(MLK_SYS_AARCH64)

/* Callee-saved set per @[AAPCS64, Section "Machine Registers"]. */
int check_aarch64_aapcs_compliance(struct aarch64_register_state *before,
                                   struct aarch64_register_state *after,
                                   int quiet)
{
  int violations = 0;
  int i;

  /* Callee-saved GPRs x19-x29, plus x18: AAPCS64 leaves x18 unspecified,
   * but Darwin reserves it and Linux/ELF leaves it unused, so we treat
   * it as callee-saved. */
  if (before->gpr[18] != after->gpr[18])
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "x18");
    violations++;
  }
  for (i = 19; i <= 29; i++)
  {
    if (before->gpr[i] != after->gpr[i])
    {
      MLK_ABI_VIOLATION(quiet, "x%d modified\n", i);
      violations++;
    }
  }

  /* The call stub leaves vector output untouched when NEON was not compiled
   * in or is unavailable at runtime. */
#if defined(MLK_SYS_AARCH64_NEON)
  if (mlk_sys_check_capability(MLK_SYS_CAP_NEON))
  {
    /* Check callee-saved NEON registers (d8-d15, lower 64 bits only). */
    for (i = 8; i <= 15; i++)
    {
      if (before->neon[i][0] != after->neon[i][0])
      {
        MLK_ABI_VIOLATION(quiet, "d%d modified\n", i);
        violations++;
      }
    }
  }
#endif /* MLK_SYS_AARCH64_NEON */

  return violations;
}

void init_aarch64_register_state(struct aarch64_register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#endif /* MLK_SYS_AARCH64 */
