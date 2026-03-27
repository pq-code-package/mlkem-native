# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = indcpa_enc_v_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mlk_indcpa_enc_v

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/indcpa.c

CHECK_FUNCTION_CONTRACTS=mlk_indcpa_enc_v
USE_FUNCTION_CONTRACTS = mlk_polyvec_frombytes
USE_FUNCTION_CONTRACTS += mlk_poly_frommsg
USE_FUNCTION_CONTRACTS += mlk_polyvec_mulcache_compute
USE_FUNCTION_CONTRACTS += mlk_polyvec_basemul_acc_montgomery_cached
USE_FUNCTION_CONTRACTS += mlk_poly_invntt_tomont
USE_FUNCTION_CONTRACTS += mlk_poly_add
USE_FUNCTION_CONTRACTS += mlk_poly_reduce
USE_FUNCTION_CONTRACTS += mlk_poly_compress_dv 
USE_FUNCTION_CONTRACTS += mlk_zeroize
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--external-smt2-solver $(PROOF_ROOT)/lib/z3_smt_only --z3

FUNCTION_NAME = mlk_indcpa_enc_v

# This function is large enough to need...
CBMC_OBJECT_BITS = 10

include ../Makefile.common
