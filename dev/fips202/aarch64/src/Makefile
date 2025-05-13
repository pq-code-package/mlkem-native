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

ALL=keccak_f1600_x1_scalar_asm.S

all: $(ALL)

purge:
	rm -rf $(ALL)
