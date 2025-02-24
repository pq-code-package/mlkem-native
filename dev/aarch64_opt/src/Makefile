# SPDX-License-Identifier: Apache-2.0

######
# To run, see the README.md file
######

# ISA to optimize for
TARGET_ISA=Arm_AArch64

# MicroArch target to optimize for
TARGET_MICROARCH=Arm_Cortex_A55

SLOTHY_FLAGS=-c sw_pipelining.enabled=true \
             -c inputs_are_outputs \
             -c reserved_regs="[x18--x30,sp]" \
             -c sw_pipelining.minimize_overlapping=False \
             -c sw_pipelining.allow_post \
             -c variable_size \
             -c constraints.stalls_first_attempt=64

COMMON_H=../../../mlkem/common.h

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

ntt.S: ../../aarch64_clean/src/ntt.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l layer123_start -l layer4567_start $(SLOTHY_FLAGS)

intt.S: ../../aarch64_clean/src/intt.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l layer123_start -l layer4567_start $(SLOTHY_FLAGS)

poly_tomont_asm.S: ../../aarch64_clean/src/poly_tomont_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l poly_tomont_asm_loop $(SLOTHY_FLAGS)

poly_reduce_asm.S: ../../aarch64_clean/src/poly_reduce_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l loop_start $(SLOTHY_FLAGS)

polyvec_basemul_acc_montgomery_cached_asm_k2.S: ../../aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l k2_loop_start $(SLOTHY_FLAGS)

polyvec_basemul_acc_montgomery_cached_asm_k3.S: ../../aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l k3_loop_start $(SLOTHY_FLAGS)

polyvec_basemul_acc_montgomery_cached_asm_k4.S: ../../aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l k4_loop_start $(SLOTHY_FLAGS)

poly_mulcache_compute_asm.S: ../../aarch64_clean/src/poly_mulcache_compute_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l mulcache_compute_loop_start $(SLOTHY_FLAGS)

poly_tobytes_asm.S: ../../aarch64_clean/src/poly_tobytes_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l poly_tobytes_asm_asm_loop_start $(SLOTHY_FLAGS) -c sw_pipelining.unroll=4

# At the moment, SLOTHY can't process rej_uniform_asm.S
rej_uniform_asm.S: ../../aarch64_clean/src/rej_uniform_asm.S $(COMMON_H)
	cp $< $@

# Extra target to test SLOTHY on rej_uniform_asm.S in future
rej_uniform_asm_with_slothy.S: ../../aarch64_clean/src/rej_uniform_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l loop48 $(SLOTHY_FLAGS)
