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
ABICHECK_REQ_MVE_FILES :=

# MVE: Armv8.1-M MVE
ABICHECK_REQ_MVE_FILES := \
  mlkem/src/fips202/native/armv81m/src/keccak_f1600_x4_mve.S \
  mlkem/src/fips202/native/armv81m/src/state_extract_bytes_x4_mve.S \
  mlkem/src/fips202/native/armv81m/src/state_xor_bytes_x4_mve.S \
  test/abicheck/armv81m/callstub_armv81m.S \
  test/abicheck/armv81m/selftest_armv81m.S
ABICHECK_REQ_MVE_OBJS := $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_REQ_MVE_FILES))
$(ABICHECK_REQ_MVE_OBJS): CFLAGS += -march=armv8.1-m.main+mve -mthumb
