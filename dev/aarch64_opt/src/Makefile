# SPDX-License-Identifier: Apache-2.0

######
# To run
#
# NOT IN THE NIX ENV
# cd $SLOTHY_ROOT
# pyenv local 3.11
# source venv/bin/activate
#
# PATH=$SLOTHY_ROOT:$PATH
# PATH=/opt/homebrew/opt/llvm/bin:$PATH
# export PATH
#
# cd $MLKEM_NATIVE_ROOT
# cd dev/aarch64_opt/src

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

all: poly_tomont_asm.S \
     poly_reduce_asm.S \
     polyvec_basemul_acc_montgomery_cached_asm_k2.S \
     polyvec_basemul_acc_montgomery_cached_asm_k3.S \
     polyvec_basemul_acc_montgomery_cached_asm_k4.S

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
