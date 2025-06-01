# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

.PHONY: all purge
.DEFAULT_GOAL := all

keccak_f1600_x1_scalar_asm.S: ../../aarch64_symbolic/keccak_f1600_x1_scalar_symbolic.S
        # The last two configuration options are for fast testing (incl. CI).
        # Remove when building a production version.

	slothy-cli Arm_AArch64 Arm_Cortex_A55 \
	   $^ -o $@ \
           -c reserved_regs="[x18,sp]" \
	   -c inputs_are_outputs \
	   -c variable_size \
	   -c constraints.stalls_first_attempt=64 \
	   -c constraints.allow_spills \
	   -c constraints.minimize_spills \
           -s keccak_f1600_x1_scalar_loop \
           -e keccak_f1600_x1_scalar_end_loop \
	   -c constraints.functional_only \
	   -c objective_lower_bound=24

	slothy-cli Arm_AArch64 Arm_Cortex_A55 \
	   $@ -o $@ \
           -c reserved_regs="[x18,sp]" \
	   -c variable_size \
	   -c inputs_are_outputs \
           -c outputs="[hint_STACK_LOC_COUNT]" \
	   -c constraints.stalls_first_attempt=64 \
	   -c constraints.allow_spills \
	   -c constraints.minimize_spills \
           -s keccak_f1600_x1_scalar_initial_start \
           -e keccak_f1600_x1_scalar_loop \
	   -c constraints.functional_only \
	   -c objective_lower_bound=24

keccak_f1600_x4_v8a_scalar_hybrid_asm.S: ../../aarch64_symbolic/keccak_f1600_x4_v8a_scalar_hybrid_clean.S
	slothy-cli Arm_AArch64 Arm_Cortex_A55 \
	   $^ -o $@                           \
	   -c reserved_regs="[x18,sp]"        \
	   -c inputs_are_outputs \
	   -c variable_size \
	   -c constraints.stalls_first_attempt=64 \
	   -c split_heuristic \
	   -c split_heuristic_repeat=0 \
	   -c split_heuristic_preprocess_naive_interleaving \
	   -c split_heuristic_preprocess_naive_interleaving_strategy="alternate" \
	   -c split_heuristic_estimate_performance=False \
	   -c absorb_spills=False \
           -c outputs="[hint_STACK_OFFSET_COUNT]" \
           -s keccak_f1600_x4_scalar_v8a_hybrid_initial \
           -e keccak_f1600_x4_scalar_v8a_hybrid_loop

	slothy-cli Arm_AArch64 Arm_Cortex_A55 \
	   $@ -o $@                           \
	   -c reserved_regs="[x18,sp]"        \
	   -c inputs_are_outputs \
	   -c variable_size \
	   -c constraints.stalls_first_attempt=64 \
	   -c split_heuristic \
	   -c split_heuristic_repeat=0 \
	   -c split_heuristic_preprocess_naive_interleaving \
	   -c split_heuristic_preprocess_naive_interleaving_strategy="alternate" \
	   -c split_heuristic_estimate_performance=False \
           -c outputs="[hint_STACK_OFFSET_COUNT]" \
	   -c absorb_spills=False \
           -s keccak_f1600_x4_scalar_v8a_hybrid_loop \
           -e keccak_f1600_x4_scalar_v8a_hybrid_loop_end

keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm.S: ../../aarch64_symbolic/keccak_f1600_x4_v8a_v84a_scalar_hybrid_clean.S
	slothy-cli Arm_AArch64 Arm_Cortex_A55 \
	   $^ -o $@                           \
	   -c reserved_regs="[x18,sp]"        \
	   -c inputs_are_outputs \
	   -c variable_size \
	   -c constraints.stalls_first_attempt=64 \
	   -c split_heuristic \
	   -c split_heuristic_repeat=0 \
	   -c split_heuristic_preprocess_naive_interleaving \
	   -c split_heuristic_preprocess_naive_interleaving_strategy="alternate" \
	   -c split_heuristic_estimate_performance=False \
	   -c absorb_spills=False \
           -c outputs="[hint_STACK_OFFSET_COUNT]" \
           -s keccak_f1600_x4_scalar_v8a_v84a_hybrid_initial \
           -e keccak_f1600_x4_scalar_v8a_v84a_hybrid_loop

	slothy-cli Arm_AArch64 Arm_Cortex_A55 \
	   $@ -o $@                           \
	   -c reserved_regs="[x18,sp]"        \
	   -c inputs_are_outputs \
	   -c variable_size \
	   -c constraints.stalls_first_attempt=64 \
	   -c split_heuristic \
	   -c split_heuristic_repeat=0 \
	   -c split_heuristic_preprocess_naive_interleaving \
	   -c split_heuristic_preprocess_naive_interleaving_strategy="alternate" \
	   -c split_heuristic_estimate_performance=False \
           -c outputs="[hint_STACK_OFFSET_COUNT]" \
	   -c absorb_spills=False \
           -s keccak_f1600_x4_scalar_v8a_v84a_hybrid_loop \
           -e keccak_f1600_x4_scalar_v8a_v84a_hybrid_loop_end

ALL=keccak_f1600_x1_scalar_asm.S                \
  keccak_f1600_x4_v8a_scalar_hybrid_asm.S       \
  keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm.S

all: $(ALL)

purge:
	rm -rf $(ALL)
