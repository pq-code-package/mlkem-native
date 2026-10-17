# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = debug_check_assert_harness

PROOF_UID = mlk_debug_check_assert

# Use native stdio declarations that match CBMC's libc model. The data-model
# stdlib.h supplies declarations for the linked libc models.
COMPILE_FLAGS = -Wall -Werror --native-compiler gcc \
	-I$(PROOF_INCLUDE) $(GOTO_CC_DM_FLAG)

DEFINES += -DMLKEM_DEBUG

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/debug.c

CHECK_FUNCTION_CONTRACTS = mlk_mlkem_debug_assert
USE_FUNCTION_CONTRACTS =
APPLY_LOOP_CONTRACTS =
USE_DYNAMIC_FRAMES = 1

# Supported CBMC configurations
CBMC_SUPPORTED_CONFIGS = LP64:z3 ILP32:z3
CBMC_DEFAULT_CONFIG = LP64:z3

FUNCTION_NAME = mlk_debug_check_assert

CBMC_OBJECT_BITS = 8

include ../Makefile.common
