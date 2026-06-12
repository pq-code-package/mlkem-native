/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [AAPCS32]
 *   Procedure Call Standard for the Arm Architecture (AAPCS32)
 *   Arm Limited
 *   https://github.com/ARM-software/abi-aa/blob/main/aapcs32/aapcs32.rst
 *
 * - [ArmARMv8M]
 *   Armv8-M Architecture Reference Manual (DDI 0553)
 *   Arm Limited
 *   https://developer.arm.com/documentation/ddi0553/latest/
 */

#include <stdio.h>

#include "../../notrandombytes/notrandombytes.h"
#include "abicheck_armv81m.h"

#if defined(MLK_SYS_ARMV81M_MVE)

/* Callee-saved set per @[AAPCS32, Section 5.1 "Machine Registers"]; MVE
 * Q-register file per @[ArmARMv8M, Section B7]. */
int check_armv81m_aapcs32_compliance(struct armv81m_register_state *before,
                                     struct armv81m_register_state *after,
                                     int quiet)
{
  int violations = 0;
  int i;

  /* Callee-saved GPRs r4-r11 (AAPCS32). r12=IP and r0-r3 are caller-saved. */
  for (i = 4; i <= 11; i++)
  {
    if (before->gpr[i] != after->gpr[i])
    {
      MLK_ABI_VIOLATION(quiet, "r%d modified\n", i);
      violations++;
    }
  }

  /* Callee-saved MVE Q-registers q4-q7 (= d8-d15). Compare full 128 bits. */
  for (i = 4; i <= 7; i++)
  {
    if (before->mve[i][0] != after->mve[i][0] ||
        before->mve[i][1] != after->mve[i][1] ||
        before->mve[i][2] != after->mve[i][2] ||
        before->mve[i][3] != after->mve[i][3])
    {
      MLK_ABI_VIOLATION(quiet, "q%d modified\n", i);
      violations++;
    }
  }

  return violations;
}

void init_armv81m_register_state(struct armv81m_register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#endif /* MLK_SYS_ARMV81M_MVE */
