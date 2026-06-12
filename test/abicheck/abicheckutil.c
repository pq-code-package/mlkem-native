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
 * - [AAPCS64]
 *   Procedure Call Standard for the Arm 64-bit Architecture (AAPCS64)
 *   Arm Limited
 *   https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst
 *
 * - [ArmARMv8M]
 *   Armv8-M Architecture Reference Manual (DDI 0553)
 *   Arm Limited
 *   https://developer.arm.com/documentation/ddi0553/latest/
 *
 * - [PPC64ELFv2]
 *   64-Bit ELFv2 ABI Specification — Power Architecture
 *   OpenPOWER Foundation
 *   https://openpowerfoundation.org/specifications/64bitelfabi/
 *
 * - [SysVAMD64]
 *   System V Application Binary Interface — AMD64 Architecture Processor
 *   Supplement
 *   Matz, Hubička, Jaeger, Mitchell
 *   https://gitlab.com/x86-psABIs/x86-64-ABI
 */

#include <stdio.h>

#include "../notrandombytes/notrandombytes.h"
#include "abicheckutil.h"

/* If quiet, suppress the per-register diagnostic. Non-variadic to stay
 * C89-clean under -pedantic; fixed names are passed via "%s". */
#define MLK_ABI_VIOLATION(quiet, fmt, arg)           \
  do                                                 \
  {                                                  \
    if (!(quiet))                                    \
    {                                                \
      fprintf(stderr, "ABI violation: " fmt, (arg)); \
    }                                                \
  } while (0)

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

  /* Check callee-saved NEON registers (d8-d15, lower 64 bits only) */
  for (i = 8; i <= 15; i++)
  {
    if (before->neon[i][0] != after->neon[i][0])
    {
      MLK_ABI_VIOLATION(quiet, "d%d modified\n", i);
      violations++;
    }
  }

  return violations;
}

void init_aarch64_register_state(struct aarch64_register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#elif defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)

/* Callee-saved set per @[SysVAMD64, Section 3.2 "Function Calling Sequence"].
 */
int check_x86_64_sysv_compliance(struct x86_64_register_state *before,
                                 struct x86_64_register_state *after, int quiet)
{
  int violations = 0;

  if (before->rbx != after->rbx)
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "rbx");
    violations++;
  }
  if (before->rbp != after->rbp)
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "rbp");
    violations++;
  }
  if (before->r12 != after->r12)
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "r12");
    violations++;
  }
  if (before->r13 != after->r13)
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "r13");
    violations++;
  }
  if (before->r14 != after->r14)
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "r14");
    violations++;
  }
  if (before->r15 != after->r15)
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "r15");
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

#elif defined(MLK_SYS_ARMV81M_MVE)

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

#endif /* !MLK_SYS_AARCH64 && !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) && \
          !MLK_SYS_PPC64LE && MLK_SYS_ARMV81M_MVE */
