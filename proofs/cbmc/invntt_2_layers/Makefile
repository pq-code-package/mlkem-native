# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = invntt_2_layers_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mlk_invntt_2_layers

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/poly.c

CHECK_FUNCTION_CONTRACTS=mlk_invntt_2_layers
USE_FUNCTION_CONTRACTS=mlk_invntt_2_layers_block
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2

FUNCTION_NAME = mlk_invntt_2_layers

CBMC_OBJECT_BITS = 8

include ../Makefile.common
