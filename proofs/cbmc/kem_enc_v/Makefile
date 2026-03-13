# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = kem_enc_v_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mlk_enc_v

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/kem.c

CHECK_FUNCTION_CONTRACTS=mlk_enc_v
USE_FUNCTION_CONTRACTS = mlk_indcpa_enc_v
USE_FUNCTION_CONTRACTS += mlk_polyvec_frombytes
USE_FUNCTION_CONTRACTS += mlk_polyvec_reduce
USE_FUNCTION_CONTRACTS += mlk_polyvec_tobytes
USE_FUNCTION_CONTRACTS += mlk_ct_memcmp
USE_FUNCTION_CONTRACTS += mlk_zeroize
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--external-smt2-solver $(PROOF_ROOT)/lib/z3_smt_only --z3

FUNCTION_NAME = mlk_enc_v

# This function is large enough to need...
CBMC_OBJECT_BITS = 12

include ../Makefile.common
