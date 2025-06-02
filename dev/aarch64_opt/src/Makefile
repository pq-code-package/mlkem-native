# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

######
# To run, see the README.md file
######
.PHONY: all clean

# ISA to optimize for
TARGET_ISA=Arm_AArch64

# MicroArch target to optimize for
TARGET_MICROARCH=Arm_Cortex_A55

SLOTHY_EXTRA_FLAGS ?=

SLOTHY_FLAGS=-c sw_pipelining.enabled=true \
             -c inputs_are_outputs \
             -c sw_pipelining.minimize_overlapping=False \
             -c sw_pipelining.allow_post \
             -c variable_size \
             -c constraints.stalls_first_attempt=64 \
             $(SLOTHY_EXTRA_FLAGS)

# For kernels which stash callee-saved v8-v15 but don't stash callee-saved GPRs x19-x30.
# Allow SLOTHY to use all V-registers, but only caller-saved GPRs.
RESERVE_X_ONLY_FLAG=-c reserved_regs="[x18--x30,sp]"

# Used for kernels which don't stash callee-saved registers.
# Restrict SLOTHY to caller-saved registers.
RESERVE_ALL_FLAG=-c reserved_regs="[x18--x30,sp,v8--v15]"

COMMON_H=../../../mlkem/src/common.h

all: ntt.S \
     intt.S \
     poly_tobytes_asm.S \
     poly_tomont_asm.S \
     poly_reduce_asm.S \
     poly_mulcache_compute_asm.S \
     polyvec_basemul_acc_montgomery_cached_asm_k2.S \
     polyvec_basemul_acc_montgomery_cached_asm_k3.S \
     polyvec_basemul_acc_montgomery_cached_asm_k4.S \
     rej_uniform_asm.S


# These units explicitly save and restore registers v8-v15, so SLOTHY can freely use
# those registers.
ntt.S: ../../aarch64_clean/src/ntt.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l ntt_layer123_start -l ntt_layer4567_start $(SLOTHY_FLAGS) $(RESERVE_X_ONLY_FLAG)

intt.S: ../../aarch64_clean/src/intt.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l intt_layer123_start -l intt_layer4567_start $(SLOTHY_FLAGS) $(RESERVE_X_ONLY_FLAG)
polyvec_basemul_acc_montgomery_cached_asm_k2.S: ../../aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l polyvec_basemul_acc_montgomery_cached_k2_loop_start $(SLOTHY_FLAGS) $(RESERVE_X_ONLY_FLAG)

polyvec_basemul_acc_montgomery_cached_asm_k3.S: ../../aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l polyvec_basemul_acc_montgomery_cached_k3_loop_start $(SLOTHY_FLAGS) $(RESERVE_X_ONLY_FLAG)

polyvec_basemul_acc_montgomery_cached_asm_k4.S: ../../aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l polyvec_basemul_acc_montgomery_cached_k4_loop_start $(SLOTHY_FLAGS) $(RESERVE_X_ONLY_FLAG)



# These units do NOT save and restore v8-v15, so we must tell SLOTHY not to use them
# to respect the ABI.
poly_tomont_asm.S: ../../aarch64_clean/src/poly_tomont_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l poly_tomont_loop $(SLOTHY_FLAGS) $(RESERVE_ALL_FLAG)

poly_reduce_asm.S: ../../aarch64_clean/src/poly_reduce_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l poly_reduce_loop_start $(SLOTHY_FLAGS) $(RESERVE_ALL_FLAG)

poly_mulcache_compute_asm.S: ../../aarch64_clean/src/poly_mulcache_compute_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l poly_mulcache_compute_loop_start $(SLOTHY_FLAGS) $(RESERVE_ALL_FLAG)

poly_tobytes_asm.S: ../../aarch64_clean/src/poly_tobytes_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l poly_tobytes_loop_start $(SLOTHY_FLAGS) $(RESERVE_ALL_FLAG) -c sw_pipelining.unroll=4

# At the moment, SLOTHY can't process rej_uniform_asm.S
rej_uniform_asm.S: ../../aarch64_clean/src/rej_uniform_asm.S $(COMMON_H)
	cp $< $@

# Extra target to test SLOTHY on rej_uniform_asm.S in future
rej_uniform_asm_with_slothy.S: ../../aarch64_clean/src/rej_uniform_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l rej_uniform_loop48 $(SLOTHY_FLAGS) $(RESERVE_ALL_FLAG)


clean:
	-$(RM) -rf *.S
