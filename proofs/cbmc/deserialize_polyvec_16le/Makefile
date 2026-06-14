# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = deserialize_polyvec_16le_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mlk_deserialize_polyvec_16le

DEFINES += -DMLK_CONFIG_ENABLE_MLKEM_BRAID
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/kem.c

CHECK_FUNCTION_CONTRACTS=mlk_deserialize_polyvec_16le
USE_FUNCTION_CONTRACTS =
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2

FUNCTION_NAME = mlk_deserialize_polyvec_16le

# This function is large enough to need...
CBMC_OBJECT_BITS = 12

include ../Makefile.common
