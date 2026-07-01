# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# WARNING: This file is auto-generated from scripts/autogen
#          in the mlkem-native repository.
#          Do not modify it directly.
#
# Edit the YAML 'ABI.Features:' list in dev/<arch>/src/<kernel>.S
# and re-run scripts/autogen instead.
#
# For each capability declared by a kernel's ABI.Features list, this
# file appends the capability's CFLAGS to that kernel's .S object
# under mlkem/src/.

# Default each cap's file list to empty so the unconditional appends
# below are safe even when a cap has no kernels on this arch.
ABICHECK_REQ_VSX_FILES :=

# VSX: PPC64 VSX/Altivec (POWER8)
ABICHECK_REQ_VSX_FILES := \
  mlkem/src/native/ppc64le/src/intt_ppc_asm.S \
  mlkem/src/native/ppc64le/src/ntt_ppc_asm.S \
  mlkem/src/native/ppc64le/src/poly_tomont_ppc_asm.S \
  mlkem/src/native/ppc64le/src/reduce_ppc_asm.S \
  test/abicheck/ppc64le/callstub_ppc64le.S \
  test/abicheck/ppc64le/selftest_ppc64le.S
ABICHECK_REQ_VSX_OBJS := $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_REQ_VSX_FILES))
$(ABICHECK_REQ_VSX_OBJS): CFLAGS += -mcpu=power8 -maltivec -mvsx
