# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# Compiler feature detection for mlkem-native
# This file detects whether the compiler supports various architectural features
# used by mlkem-native through compile-time tests with C code containing inline assembly.
#
# Feature detection can be overridden by setting the corresponding variable on the command line:
#   make MK_COMPILER_SUPPORTS_SHA3=0    # Disable SHA3 detection
#   make MK_COMPILER_SUPPORTS_AVX2=0    # Disable AVX2 detection
#   make MK_COMPILER_SUPPORTS_BMI2=0    # Disable BMI2 detection
#   make MK_COMPILER_SUPPORTS_SSE2=0    # Disable SSE2 detection

ifndef _COMPILER_MK
_COMPILER_MK :=

# Normalize architecture names
ARCH := $(shell uname -m)
ifeq ($(ARCH),arm64)
ARCH := aarch64
endif

# Override ARCH for cross-compilation based on CROSS_PREFIX
ifneq ($(CROSS_PREFIX),)
ifneq ($(findstring x86_64, $(CROSS_PREFIX)),)
ARCH := x86_64
else ifneq ($(findstring aarch64_be, $(CROSS_PREFIX)),)
ARCH := aarch64_be
else ifneq ($(findstring aarch64, $(CROSS_PREFIX)),)
ARCH := aarch64
else ifneq ($(findstring riscv64, $(CROSS_PREFIX)),)
ARCH := riscv64
else ifneq ($(findstring riscv32, $(CROSS_PREFIX)),)
ARCH := riscv32
else ifneq ($(findstring powerpc64le, $(CROSS_PREFIX)),)
ARCH := powerpc64le
endif
endif # CROSS_PREFIX

# x86_64 feature detection
ifeq ($(ARCH),x86_64)

# Test AVX2 support using C with inline assembly
# Can be overridden by setting MK_COMPILER_SUPPORTS_AVX2=0/1 on command line
MK_COMPILER_SUPPORTS_AVX2 ?= $(shell echo 'int main() { __asm__("vpxor %%ymm0, %%ymm1, %%ymm2" ::: "ymm0", "ymm1", "ymm2"); return 0; }' | $(CC) -mavx2 -x c - -c -o /dev/null 2>/dev/null && echo 1 || echo 0)

# Test SSE2 support using C with inline assembly
# Can be overridden by setting MK_COMPILER_SUPPORTS_SSE2=0/1 on command line
MK_COMPILER_SUPPORTS_SSE2 ?= $(shell echo 'int main() { __asm__("pxor %%xmm0, %%xmm1" ::: "xmm0", "xmm1"); return 0; }' | $(CC) -msse2 -x c - -c -o /dev/null 2>/dev/null && echo 1 || echo 0)

# Test BMI2 support using C with inline assembly
# Can be overridden by setting MK_COMPILER_SUPPORTS_BMI2=0/1 on command line
MK_COMPILER_SUPPORTS_BMI2 ?= $(shell echo 'int main() { __asm__("pdep %%eax, %%ebx, %%ecx" ::: "eax", "ebx", "ecx"); return 0; }' | $(CC) -mbmi2 -x c - -c -o /dev/null 2>/dev/null && echo 1 || echo 0)

endif # x86_64

# AArch64 feature detection
ifeq ($(ARCH),aarch64)

# Test SHA3 support (Armv8.4-a+SHA3) using C with inline assembly
# Can be overridden by setting MK_COMPILER_SUPPORTS_SHA3=0/1 on command line
MK_COMPILER_SUPPORTS_SHA3 ?= $(shell echo 'int main() { __asm__("eor3 v0.16b, v1.16b, v2.16b, v3.16b" ::: "v0", "v1", "v2", "v3"); return 0; }' | $(CC) -march=armv8.4-a+sha3 -x c - -c -o /dev/null 2>/dev/null && echo 1 || echo 0)

endif # aarch64

endif # _COMPILER_MK
