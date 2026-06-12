/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [PPC64ELFv2]
 *   64-Bit ELFv2 ABI Specification — Power Architecture
 *   OpenPOWER Foundation
 *   https://openpowerfoundation.org/specifications/64bitelfabi/
 */

#include <stdio.h>

#include "../../notrandombytes/notrandombytes.h"
#include "abicheck_ppc64le.h"

#if defined(MLK_SYS_PPC64LE)

/* Non-volatile condition register fields CR2, CR3, CR4. In the 32-bit condition
 * register, field CRn occupies bits [4n, 4n+3] (CR0 most significant), so
 * CR2|CR3|CR4 form the mask below. CR0/CR1 and CR5-CR7 are volatile. */
#define MLK_PPC_CR_NV_MASK 0x00fff000u

/* Callee-saved set per @[PPC64ELFv2, Section 2.2 "Register Usage"]. */
int check_ppc64le_elfv2_compliance(struct ppc64le_register_state *before,
                                   struct ppc64le_register_state *after,
                                   int quiet)
{
  int violations = 0;
  int i;

  /* Non-volatile GPRs r14-r31 */
  for (i = 0; i < 18; i++)
  {
    if (before->gpr_nv[i] != after->gpr_nv[i])
    {
      MLK_ABI_VIOLATION(quiet, "r%d modified\n", i + 14);
      violations++;
    }
  }

  /* Non-volatile FPRs f14-f31 */
  for (i = 0; i < 18; i++)
  {
    if (before->fpr[i] != after->fpr[i])
    {
      MLK_ABI_VIOLATION(quiet, "f%d modified\n", i + 14);
      violations++;
    }
  }

  /* Non-volatile VRs v20-v31 (full 128 bits) */
  for (i = 0; i < 12; i++)
  {
    if (before->vr[i][0] != after->vr[i][0] ||
        before->vr[i][1] != after->vr[i][1])
    {
      MLK_ABI_VIOLATION(quiet, "v%d modified\n", i + 20);
      violations++;
    }
  }

  /* Non-volatile condition register fields CR2-CR4 */
  if ((before->cr & MLK_PPC_CR_NV_MASK) != (after->cr & MLK_PPC_CR_NV_MASK))
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "CR2-CR4");
    violations++;
  }

  return violations;
}

void init_ppc64le_register_state(struct ppc64le_register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#endif /* MLK_SYS_PPC64LE */
