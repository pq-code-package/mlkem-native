/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include <stdio.h>

#include "../notrandombytes/notrandombytes.h"
#include "abicheckutil.h"

#if defined(MLK_SYS_AARCH64)

int check_aarch64_aapcs_compliance(struct register_state *before,
                                   struct register_state *after)
{
  int violations = 0;
  int i;

  /* Check callee-saved general-purpose registers (x19-x29) */
  for (i = 19; i <= 29; i++)
  {
    if (before->gpr[i] != after->gpr[i])
    {
      printf("ABI violation: x%d modified\n", i);
      violations++;
    }
  }

  /* Check callee-saved NEON registers (d8-d15, lower 64 bits only) */
  for (i = 8; i <= 15; i++)
  {
    if (before->neon[i][0] != after->neon[i][0])
    {
      printf("ABI violation: d%d modified\n", i);
      violations++;
    }
  }

  return violations;
}

void init_register_state(struct register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#elif defined(MLK_SYS_X86_64)

int check_x86_64_sysv_compliance(struct x86_64_register_state *before,
                                 struct x86_64_register_state *after)
{
  int violations = 0;

  if (before->rbx != after->rbx)
  {
    printf("ABI violation: rbx modified\n");
    violations++;
  }
  if (before->rbp != after->rbp)
  {
    printf("ABI violation: rbp modified\n");
    violations++;
  }
  if (before->r12 != after->r12)
  {
    printf("ABI violation: r12 modified\n");
    violations++;
  }
  if (before->r13 != after->r13)
  {
    printf("ABI violation: r13 modified\n");
    violations++;
  }
  if (before->r14 != after->r14)
  {
    printf("ABI violation: r14 modified\n");
    violations++;
  }
  if (before->r15 != after->r15)
  {
    printf("ABI violation: r15 modified\n");
    violations++;
  }

  return violations;
}

void init_x86_64_register_state(struct x86_64_register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#endif /* !MLK_SYS_AARCH64 && MLK_SYS_X86_64 */
