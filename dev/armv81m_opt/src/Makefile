# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

######
# To run, see the README.md file
######
.PHONY: all clean

# ISA to optimize for
TARGET_ISA=Arm_v81M

# MicroArch target to optimize for
TARGET_MICROARCH=Arm_Cortex_M55

SLOTHY_EXTRA_FLAGS ?=

SLOTHY_FLAGS= \
              -c unsafe_address_offset_fixup = False \
              -c inputs_are_outputs = True \
              -c allow_useless_instructions = True \
              -c constraints.functional_only = False \
              -c constraints.allow_reordering = True \
              -c variable_size = True \
              -c constraints.stalls_first_attempt = 64 \
              -c constraints.max_displacement = 1 \
              -c constraints.stalls_maximum_attempt = 4096 \
              -c split_heuristic = True \
              -c split_heuristic_stepsize = 0.05 \
              -c split_heuristic_factor = 20 \
              -c split_heuristic_repeat = 2 \
              -c split_heuristic_estimate_performance = False \
              -c split_heuristic_optimize_seam = 2 \
             $(SLOTHY_EXTRA_FLAGS)

COMMON_H=../../../mlkem/src/common.h

all: mve-keccak-4x.S \
     bit_interleave_4x.S \

mve-keccak-4x.S: ../../armv81m_clean/src/mve-keccak-4x.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -s roundstart -e roundend_pre $(SLOTHY_FLAGS)

bit_interleave_4x.S: ../../armv81m_clean/src/mve-keccak-4x.S $(COMMON_H)
     slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ \
          -se to_bit_interleaving_4x_start,to_bit_interleaving_4x_exit \
          -se from_bit_interleaving_4x_start,from_bit_interleaving_4x_exit \
          $(SLOTHY_FLAGS)

clean:
	-$(RM) -rf *.S
