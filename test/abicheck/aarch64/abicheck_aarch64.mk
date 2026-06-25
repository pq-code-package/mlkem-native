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
ABICHECK_REQ_SHA3_FILES :=

# SHA3: Armv8.4-A SHA3 (eor3, rax1, xar, bcax)
ABICHECK_REQ_SHA3_FILES := \
  mlkem/src/fips202/native/aarch64/src/keccak_f1600_x1_v84a_aarch64_asm.S \
  mlkem/src/fips202/native/aarch64/src/keccak_f1600_x2_v84a_aarch64_asm.S \
  mlkem/src/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_aarch64_asm.S
ABICHECK_REQ_SHA3_OBJS := $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_REQ_SHA3_FILES))
$(ABICHECK_REQ_SHA3_OBJS): CFLAGS += -march=armv8.4-a+sha3
