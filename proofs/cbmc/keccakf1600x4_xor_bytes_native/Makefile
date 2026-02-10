# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = keccakf1600x4_xor_bytes_native_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = keccakf1600x4_xor_bytes_native

DEFINES += -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 -DMLK_CONFIG_FIPS202_BACKEND_FILE="\"dummy_backend_fips202_x4.h\""
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/fips202/keccakf1600.c

CHECK_FUNCTION_CONTRACTS=mlk_keccakf1600x4_xor_bytes
USE_FUNCTION_CONTRACTS=mlk_keccakf1600_xor_bytes_x4_native
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--bitwuzla

FUNCTION_NAME = keccakf1600x4_xor_bytes_native

# This function is large enough to need...
CBMC_OBJECT_BITS = 8

include ../Makefile.common
