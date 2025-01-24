#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

#
# This Makefile is derived from the Makefile arm/Makefile in s2n-bignum.
# - Remove all s2n-bignum proofs and tutorial, add mlkem-native proofs
# - Minor path modifications to support base theories from s2n-bignum
#   to reside in a separate read-only directory
#

OSTYPE_RESULT=$(shell uname -s)
ARCHTYPE_RESULT=$(shell uname -m)

SRC ?= $(S2N_BIGNUM_DIR)
SRC_ARM ?= $(SRC)/arm

# Add explicit language input parameter to cpp, otherwise the use of #n for
# numeric literals in ARM code is a problem when used inside #define macros
# since normally that means stringization.
#
# Some clang-based preprocessors seem to behave differently, and get confused
# by single-quote characters in comments, so we eliminate // comments first.

ifeq ($(OSTYPE_RESULT),Darwin)
PREPROCESS=sed -e 's/\/\/.*//' | $(CC) -E -I$(SRC)/include $(SYMBOL_HIDING) -xassembler-with-cpp -
else
PREPROCESS=$(CC) -E -I$(SRC)/include $(SYMBOL_HIDING) -xassembler-with-cpp -
endif

# Generally GNU-type assemblers are happy with multiple instructions on
# a line, but we split them up anyway just in case.

SPLIT=tr ';' '\n'

# If actually on an ARM8 machine, just use the assembler (as). Otherwise
# use a cross-assembling version so that the code can still be assembled
# and the proofs checked against the object files (though you won't be able
# to run code without additional emulation infrastructure). For the clang
# version on OS X we just add the "-arch arm64" option. For the Linux/gcc
# toolchain we assume the presence of the special cross-assembler. This
# can be installed via something like:
#
#  sudo apt-get install binutils-aarch64-linux-gnu

ifeq ($(ARCHTYPE_RESULT),aarch64)
ASSEMBLE=as
OBJDUMP=objdump -d
else
ifeq ($(ARCHTYPE_RESULT),arm64)
ASSEMBLE=as
OBJDUMP=objdump -d
else
ifeq ($(OSTYPE_RESULT),Darwin)
ASSEMBLE=as -arch arm64
OBJDUMP=otool -tvV
else
ASSEMBLE=aarch64-linux-gnu-as
OBJDUMP=aarch64-linux-gnu-objdump -d
endif
endif
endif

OBJ = mlkem/mlkem_ntt.o

# According to
# https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms,
# x18 should not be used for Apple platforms. Check this using grep.
$(OBJ): %.o : %.S
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	cat $< | $(PREPROCESS) | $(SPLIT) | grep -v -E '^\s+.quad\s+0x[0-9a-f]+$$' | $(ASSEMBLE) -o $@ -
	$(OBJDUMP) $@ | ( ( ! grep --ignore-case -E 'w18|[^0]x18' ) || ( rm $@ ; exit 1 ) )
	cat $< | $(PREPROCESS) | $(SPLIT) | $(ASSEMBLE) -o $@ -

clean:; rm -f */*.o */*/*.o */*.correct */*.native

# Proof-related parts
#
# The proof files are all independent, though each one loads the
# same common infrastructure "base.ml". So you can potentially
# run the proofs in parallel for more speed, e.g.
#
#    nohup make -j 16 proofs &
#
# If you build hol-light yourself (see https://github.com/jrh13/hol-light)
# in your home directory, and do "make" inside the subdirectory hol-light,
# then the following HOLDIR setting should be right:

HOLDIR?=$(HOLLIGHTDIR)
HOLLIGHT:=$(HOLDIR)/hol.sh

BASE?=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

PROOF_BINS = $(OBJ:.o=.native)
PROOF_LOGS = $(OBJ:.o=.correct)

# Build precompiled native binaries of HOL Light proofs

proofs/simulator.native: $(SRC_ARM)/proofs/simulator.ml
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(SRC)/tools/build-proof.sh $(SRC_ARM)/proofs/simulator.ml "$(HOLLIGHT)" "$@"

#mlkem/mlkem_ntt.native: proofs/mlkem_ntt.ml mlkem/mlkem_ntt.o; $(SRC)/tools/build-proof.sh proofs/mlkem_ntt.ml "$(HOLLIGHT)" "$@"

.SECONDEXPANSION:
%.native: proofs/$$(*F).ml %.o ; $(SRC)/tools/build-proof.sh $(BASE)/$< "$(HOLLIGHT)" "$@"

# Run them and print the standard output+error at *.correct
%.correct: %.native ; $(SRC)/tools/run-proof.sh "$(BASE)/$<" "$@"

build_proofs: $(UNOPT_OBJ) $(PROOF_BINS);
run_proofs: build_proofs $(PROOF_LOGS);

proofs: run_proofs ; $(SRC)/tools/count-proofs.sh .

# Always run sematest regardless of dependency check
FORCE: ;
# Always use max. # of cores because in Makefile one cannot get the passed number of -j.
# A portable way of getting the number of max. cores:
# https://stackoverflow.com/a/23569003/1488216
NUM_CORES_FOR_SEMATEST = $(shell getconf _NPROCESSORS_ONLN)
sematest: FORCE $(OBJ) $(SRC_ARM)/proofs/simulator_iclasses.ml $(SRC_ARM)/proofs/simulator.native
	$(SRC)/tools/run-sematest.sh arm $(NUM_CORES_FOR_SEMATEST)
