# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

.PHONY: all purge FORCE
.DEFAULT_GOAL := all

# ISA to optimize for
TARGET_ISA=Arm_v81M

# MicroArch target to optimize for
TARGET_MICROARCH=Arm_Cortex_M55
keccak_f1600_x4_mve.S: ../../armv81m_symbolic/keccak_f1600_x4_mve_clean.S
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $(TMP) \
		-s keccak_f1600_x4_mve_asm_roundstart \
		-e keccak_f1600_x4_mve_asm_roundend_pre \
		-c unsafe_address_offset_fixup=False \
		-c inputs_are_outputs=True \
		-c constraints.functional_only=True \
		-c constraints.allow_reordering=True \
		-c constraints.max_displacement=0.1
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $(TMP) -o $@ \
		-s keccak_f1600_x4_mve_asm_roundstart \
		-e keccak_f1600_x4_mve_asm_roundend_pre \
		-c constraints.functional_only=False \
		-c constraints.allow_reordering=True \
		-c variable_size=True \
        -c inputs_are_outputs=True \
		-c constraints.stalls_first_attempt=64 \
		-c constraints.max_displacement=1.0 \
		-c constraints.stalls_maximum_attempt=4096 \
        -c unsafe_address_offset_fixup=False \
		-c split_heuristic=True \
		-c split_heuristic_stepsize=0.05 \
		-c split_heuristic_factor=26 \
		-c split_heuristic_repeat=2 \
		-c split_heuristic_estimate_performance=False \
		-c split_heuristic_optimize_seam=2
	rm -f $(TMP)

# -----------------------------------------------------------------------------
# SLOTHY optimization for x1 MVE byte ops
# -----------------------------------------------------------------------------
# We optimize only the hot main loops, keeping prologue/epilogue intact.
# These targets operate in-place on the dev sources using a temporary file.
# The FORCE prerequisite ensures they rebuild when explicitly requested.

state_xor_bytes_x1_mve_asm.S: ../../armv81m_symbolic/src/state_xor_bytes_x1_mve_asm.S
	$(eval TMP := $(shell mktemp))
	# Pass 1: functional constraints only, stabilize schedule
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $(TMP) \
		-s keccak_f1600_x1_state_xor_bytes_asm_main_loop_start \
		-e keccak_f1600_x1_state_xor_bytes_asm_main_loop_end_pre \
		-c unsafe_address_offset_fixup=False \
		-c inputs_are_outputs=True \
		-c constraints.functional_only=True \
		-c constraints.allow_reordering=True \
		-c constraints.max_displacement=0.1
	# Pass 2: full optimization with splitting heuristics
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $(TMP) -o $@ \
		-s keccak_f1600_x1_state_xor_bytes_asm_main_loop_start \
		-e keccak_f1600_x1_state_xor_bytes_asm_main_loop_end_pre \
		-c constraints.functional_only=False \
		-c constraints.allow_reordering=True \
		-c variable_size=True \
		-c inputs_are_outputs=True \
		-c constraints.stalls_first_attempt=64 \
		-c constraints.max_displacement=1.0 \
		-c constraints.stalls_maximum_attempt=4096 \
		-c unsafe_address_offset_fixup=False \
		-c split_heuristic=True \
		-c split_heuristic_stepsize=0.05 \
		-c split_heuristic_factor=26 \
		-c split_heuristic_repeat=2 \
		-c split_heuristic_estimate_performance=False \
		-c split_heuristic_optimize_seam=2
	rm -f $(TMP)

state_extract_bytes_x1_mve_asm.S: ../../armv81m_symbolic/src/state_extract_bytes_x1_mve_asm.S
	$(eval TMP := $(shell mktemp))
	# Pass 1: functional constraints only, stabilize schedule
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $(TMP) \
		-s keccak_f1600_x1_state_extract_bytes_asm_main_loop_start \
		-e keccak_f1600_x1_state_extract_bytes_asm_main_loop_end_pre \
		-c unsafe_address_offset_fixup=False \
		-c inputs_are_outputs=True \
		-c constraints.functional_only=True \
		-c constraints.allow_reordering=True \
		-c constraints.max_displacement=0.1
	# Pass 2: full optimization with splitting heuristics
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $(TMP) -o $@ \
		-s keccak_f1600_x1_state_extract_bytes_asm_main_loop_start \
		-e keccak_f1600_x1_state_extract_bytes_asm_main_loop_end_pre \
		-c constraints.functional_only=False \
		-c constraints.allow_reordering=True \
		-c variable_size=True \
		-c inputs_are_outputs=True \
		-c constraints.stalls_first_attempt=64 \
		-c constraints.max_displacement=1.0 \
		-c constraints.stalls_maximum_attempt=4096 \
		-c unsafe_address_offset_fixup=False \
		-c split_heuristic=True \
		-c split_heuristic_stepsize=0.05 \
		-c split_heuristic_factor=26 \
		-c split_heuristic_repeat=2 \
		-c split_heuristic_estimate_performance=False \
		-c split_heuristic_optimize_seam=2
	rm -f $(TMP)

ALL=state_xor_bytes_x1_mve_asm.S \
	state_extract_bytes_x1_mve_asm.S
all: $(ALL)

purge:
	rm -rf $(ALL)

# Phony prerequisite used to force re-optimization when invoked explicitly.
FORCE:
