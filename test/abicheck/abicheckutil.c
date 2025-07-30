/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#include "../notrandombytes/notrandombytes.h"
#include "abicheckutil.h"

/* AArch64 AAPCS callee-saved registers: */
/* - General-purpose: x19-x28, x29 (FP), x30 (LR) */
/* - NEON: d8-d15 (lower 64 bits of q8-q15 only) */

int check_aarch64_aapcs_compliance(struct register_state *before,
                                   struct register_state *after)
{
  int violations = 0;
  int i;

  /* Check callee-saved general-purpose registers (x19-x30) */
  /* Also, check that x18 has not been touched */
  for (i = 18; i <= 29; i++)
  {
    if (before->gpr[i] != after->gpr[i])
    {
      printf("ABI violation: x%d changed from 0x%016" PRIx64 " to 0x%016" PRIx64
             "\n",
             i, before->gpr[i], after->gpr[i]);
      violations++;
    }
  }

  /* Check callee-saved NEON registers (d8-d15, lower 64 bits only) */
  /* AAPCS only requires preservation of d8-d15, not the full q8-q15 */
  for (i = 8; i <= 15; i++)
  {
    if (before->neon[i][0] != after->neon[i][0])
    {
      printf("ABI violation: d%d changed from 0x%016" PRIx64 " to 0x%016" PRIx64
             "\n",
             i, before->neon[i][0], after->neon[i][0]);
      violations++;
    }
  }

  return violations;
}

void init_random_register_state(struct register_state *state)
{
  int i;

  /* Set Xi = i for GPRs */
  for (i = 0; i < 31; i++)
  {
    state->gpr[i] = i;
  }

  /* Set NEON registers to predictable values */
  for (i = 0; i < 32; i++)
  {
    state->neon[i][0] = i;       /* Lower 64 bits = i */
    state->neon[i][1] = i + 100; /* Upper 64 bits = i + 100 */
  }
}
