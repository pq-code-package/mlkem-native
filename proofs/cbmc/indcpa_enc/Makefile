# SPDX-License-Identifier: Apache-2.0

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = indcpa_enc_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = indcpa_enc

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/indcpa.c

CHECK_FUNCTION_CONTRACTS=$(MLK_NAMESPACE)indcpa_enc

USED_FUNCTIONS = poly_frommsg
USED_FUNCTIONS += ct_zeroize
USED_FUNCTIONS += gen_matrix
ifeq ($(MLKEM_K),2)
USED_FUNCTIONS += poly_getnoise_eta1122_4x
USED_FUNCTIONS += poly_getnoise_eta2
else ifeq ($(MLKEM_K),3)
USED_FUNCTIONS += poly_getnoise_eta1_4x
else ifeq ($(MLKEM_K),4)
USED_FUNCTIONS += poly_getnoise_eta1_4x
USED_FUNCTIONS += poly_getnoise_eta2
endif

USED_FUNCTIONS += polyvec_ntt
USED_FUNCTIONS += polyvec_mulcache_compute
USED_FUNCTIONS += polyvec_basemul_acc_montgomery_cached
USED_FUNCTIONS += polyvec_invntt_tomont
USED_FUNCTIONS += poly_invntt_tomont
USED_FUNCTIONS += polyvec_add
USED_FUNCTIONS += poly_add
USED_FUNCTIONS += polyvec_reduce
USED_FUNCTIONS += poly_reduce
USED_FUNCTIONS += polyvec_compress_du
USED_FUNCTIONS += poly_compress_dv
USED_FUNCTIONS += polyvec_frombytes
USED_FUNCTIONS += matvec_mul

USE_FUNCTION_CONTRACTS=$(addprefix $(MLK_NAMESPACE),$(USED_FUNCTIONS))
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2

FUNCTION_NAME = $(MLK_NAMESPACE)indcpa_enc

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

# This function is large enough to need...
CBMC_OBJECT_BITS = 10

# If you require access to a file-local ("static") function or object to conduct
# your proof, set the following (and do not include the original source file
# ("mlkem/poly.c") in PROJECT_SOURCES).
# REWRITTEN_SOURCES = $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i
# include ../Makefile.common
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_SOURCE = $(SRCDIR)/mlkem/poly.c
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_FUNCTIONS = foo bar
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_OBJECTS = baz
# Care is required with variables on the left-hand side: REWRITTEN_SOURCES must
# be set before including Makefile.common, but any use of variables on the
# left-hand side requires those variables to be defined. Hence, _SOURCE,
# _FUNCTIONS, _OBJECTS is set after including Makefile.common.

include ../Makefile.common
