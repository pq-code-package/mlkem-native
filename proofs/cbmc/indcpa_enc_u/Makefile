# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = indcpa_enc_u_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = mlk_indcpa_enc_u

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/src/indcpa.c

CHECK_FUNCTION_CONTRACTS=mlk_indcpa_enc_u
USE_FUNCTION_CONTRACTS = mlk_gen_matrix
ifeq ($(MLKEM_K),2)
USE_FUNCTION_CONTRACTS += mlk_poly_getnoise_eta1122_4x
USE_FUNCTION_CONTRACTS += mlk_poly_getnoise_eta2
else ifeq ($(MLKEM_K),3)
USE_FUNCTION_CONTRACTS += mlk_poly_getnoise_eta1_4x
else ifeq ($(MLKEM_K),4)
USE_FUNCTION_CONTRACTS += mlk_poly_getnoise_eta1_4x
USE_FUNCTION_CONTRACTS += mlk_poly_getnoise_eta2
endif

USE_FUNCTION_CONTRACTS += mlk_polyvec_ntt
USE_FUNCTION_CONTRACTS += mlk_polyvec_mulcache_compute
USE_FUNCTION_CONTRACTS += mlk_matvec_mul
USE_FUNCTION_CONTRACTS += mlk_polyvec_invntt_tomont
USE_FUNCTION_CONTRACTS += mlk_polyvec_add
USE_FUNCTION_CONTRACTS += mlk_polyvec_reduce
USE_FUNCTION_CONTRACTS += mlk_polyvec_compress_du
USE_FUNCTION_CONTRACTS += mlk_zeroize
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--external-smt2-solver $(PROOF_ROOT)/lib/z3_smt_only --z3

FUNCTION_NAME = mlk_indcpa_enc_u

# This function is large enough to need...
CBMC_OBJECT_BITS = 12

include ../Makefile.common
