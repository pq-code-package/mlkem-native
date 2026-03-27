# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = kem_enc_derand_u_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mlk_enc_derand_u

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/kem.c

CHECK_FUNCTION_CONTRACTS=mlk_enc_derand_u
USE_FUNCTION_CONTRACTS = mlk_indcpa_enc_u
USE_FUNCTION_CONTRACTS += mlk_sha3_512
USE_FUNCTION_CONTRACTS += mlk_polyvec_reduce
USE_FUNCTION_CONTRACTS += mlk_zeroize
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2

FUNCTION_NAME = mlk_enc_derand_u

# This function is large enough to need...
CBMC_OBJECT_BITS = 10

include ../Makefile.common
