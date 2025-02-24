######
# To run
#
# NOT IN THE NIX ENV
# cd $SLOTHY_ROOT
# pyenv local 3.11
# PATH=$SLOTHY_ROOT:$PATH
# PATH=/opt/homebrew/opt/llvm/bin:$PATH
# export PATH
#
# cd $MLKEM_NATIVE_ROOT
# cd dev/aarch64_opt/src

#



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

all: poly_tomont_asm.S poly_reduce_asm.S

poly_tomont_asm.S: ../../aarch64_clean/src/poly_tomont_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l poly_tomont_asm_loop $(SLOTHY_FLAGS)

poly_reduce_asm.S: ../../aarch64_clean/src/poly_reduce_asm.S $(COMMON_H)
	slothy-cli $(TARGET_ISA) $(TARGET_MICROARCH) $< -o $@ -l loop_start $(SLOTHY_FLAGS)
