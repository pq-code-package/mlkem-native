# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = poly_decompress_d10_native_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mlk_poly_decompress_d10_native

DEFINES += -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_ARITH_BACKEND_FILE="\"dummy_backend.h\""
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/compress.c

ifneq ($(MLKEM_K),4)
CHECK_FUNCTION_CONTRACTS=mlk_poly_decompress_d10
USE_FUNCTION_CONTRACTS = mlk_poly_decompress_d10_native
USE_FUNCTION_CONTRACTS += mlk_poly_decompress_d10_c
else
CHECK_FUNCTION_CONTRACTS=
USE_FUNCTION_CONTRACTS=
endif
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--bitwuzla

FUNCTION_NAME = mlk_poly_decompress_d10_native

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

# This function is large enough to need...
CBMC_OBJECT_BITS = 8

include ../Makefile.common
