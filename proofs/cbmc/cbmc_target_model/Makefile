# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = cbmc_target_model_harness

PROOF_UID = mlk_cbmc_target_model

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(PROOFDIR)/cbmc_target_model_project.c

EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2

FUNCTION_NAME = harness

CBMC_OBJECT_BITS = 8

include ../Makefile.common
