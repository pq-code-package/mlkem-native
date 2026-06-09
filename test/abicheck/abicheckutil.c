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

#elif defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)

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

#elif defined(MLK_SYS_PPC64LE)

/* Non-volatile condition register fields CR2, CR3, CR4. In the 32-bit condition
 * register, field CRn occupies bits [4n, 4n+3] (CR0 most significant), so
 * CR2|CR3|CR4 form the mask below. CR0/CR1 and CR5-CR7 are volatile. */
#define MLK_PPC_CR_NV_MASK 0x00fff000u

int check_ppc64le_elfv2_compliance(struct ppc64le_register_state *before,
                                   struct ppc64le_register_state *after)
{
  int violations = 0;
  int i;

  /* Non-volatile GPRs r14-r31 */
  for (i = 0; i < 18; i++)
  {
    if (before->gpr_nv[i] != after->gpr_nv[i])
    {
      printf("ABI violation: r%d modified\n", i + 14);
      violations++;
    }
  }

  /* Non-volatile FPRs f14-f31 */
  for (i = 0; i < 18; i++)
  {
    if (before->fpr[i] != after->fpr[i])
    {
      printf("ABI violation: f%d modified\n", i + 14);
      violations++;
    }
  }

  /* Non-volatile VRs v20-v31 (full 128 bits) */
  for (i = 0; i < 12; i++)
  {
    if (before->vr[i][0] != after->vr[i][0] ||
        before->vr[i][1] != after->vr[i][1])
    {
      printf("ABI violation: v%d modified\n", i + 20);
      violations++;
    }
  }

  /* Non-volatile condition register fields CR2-CR4 */
  if (((uint32_t)before->cr & MLK_PPC_CR_NV_MASK) !=
      ((uint32_t)after->cr & MLK_PPC_CR_NV_MASK))
  {
    printf("ABI violation: CR2-CR4 modified\n");
    violations++;
  }

  return violations;
}

void init_ppc64le_register_state(struct ppc64le_register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#endif /* !MLK_SYS_AARCH64 && !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) && \
          MLK_SYS_PPC64LE */
