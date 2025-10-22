# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# Automatically detect system architecture and set preprocessor flags accordingly
# This file detects host CPU capabilities and combines them with compiler support
# to enable optimal compilation flags.

ifndef _AUTO_MK
_AUTO_MK :=

# Helper function to check if host CPU supports a feature
# Usage: $(call check_host_feature,feature_pattern,source_command)
define check_host_feature
$(shell $(2) 2>/dev/null | grep -q "$(1)" && echo 1 || echo 0)
endef

# x86_64 architecture detection
ifeq ($(ARCH),x86_64)

# Host CPU feature detection for x86_64
ifeq ($(HOST_PLATFORM),Linux-x86_64)
# Linux: Use /proc/cpuinfo
MK_HOST_SUPPORTS_AVX2 := $(call check_host_feature,avx2,cat /proc/cpuinfo)
MK_HOST_SUPPORTS_SSE2 := $(call check_host_feature,sse2,cat /proc/cpuinfo)
MK_HOST_SUPPORTS_BMI2 := $(call check_host_feature,bmi2,cat /proc/cpuinfo)
else ifeq ($(HOST_PLATFORM),Darwin-x86_64)
# macOS: Use sysctl
MK_HOST_SUPPORTS_AVX2 := $(call check_host_feature,AVX2,sysctl -n machdep.cpu.leaf7_features)
MK_HOST_SUPPORTS_SSE2 := $(call check_host_feature,SSE2,sysctl -n machdep.cpu.features)
MK_HOST_SUPPORTS_BMI2 := $(call check_host_feature,BMI2,sysctl -n machdep.cpu.leaf7_features)
else ifneq ($(CROSS_PREFIX),)
# Cross-compilation: assume all features are supported
MK_HOST_SUPPORTS_AVX2 := 1
MK_HOST_SUPPORTS_SSE2 := 1
MK_HOST_SUPPORTS_BMI2 := 1
else
# Other platforms: assume no support
MK_HOST_SUPPORTS_AVX2 := 0
MK_HOST_SUPPORTS_SSE2 := 0
MK_HOST_SUPPORTS_BMI2 := 0
endif # HOST_PLATFORM x86_64

endif # x86_64

# AArch64 architecture detection
ifeq ($(ARCH),aarch64)

# Host CPU feature detection for AArch64
ifeq ($(HOST_PLATFORM),Linux-aarch64)
# Linux: Use /proc/cpuinfo (look for sha3 in Features line)
MK_HOST_SUPPORTS_SHA3 := $(call check_host_feature,sha3,cat /proc/cpuinfo)
else ifeq ($(HOST_PLATFORM),Darwin-arm64)
# macOS: Use sysctl to check for SHA3 support
MK_HOST_SUPPORTS_SHA3 := $(call check_host_feature,1,sysctl -n hw.optional.armv8_2_sha3)
else ifneq ($(CROSS_PREFIX),)
# Cross-compilation: assume all features are supported
MK_HOST_SUPPORTS_SHA3 := 1
else
# Other platforms: assume no support
MK_HOST_SUPPORTS_SHA3 := 0
endif # HOST_PLATFORM aarch64

endif # aarch64

# Only apply CFLAGS modifications if AUTO=1
ifeq ($(AUTO),1)

# x86_64 CFLAGS configuration
ifeq ($(ARCH),x86_64)
CFLAGS += -DMLK_FORCE_X86_64

# Add flags only if both compiler and host support the feature
ifeq ($(MK_COMPILER_SUPPORTS_AVX2)$(MK_HOST_SUPPORTS_AVX2),11)
CFLAGS += -mavx2
endif

ifeq ($(MK_COMPILER_SUPPORTS_BMI2)$(MK_HOST_SUPPORTS_BMI2),11)
CFLAGS += -mbmi2
endif
endif # x86_64

# AArch64 CFLAGS configuration
ifeq ($(ARCH),aarch64)
CFLAGS += -DMLK_FORCE_AARCH64

# Add SHA3 flags only if both compiler and host support it
ifeq ($(MK_COMPILER_SUPPORTS_SHA3)$(MK_HOST_SUPPORTS_SHA3),11)
CFLAGS += -march=armv8.4-a+sha3
endif
endif # aarch64

# AArch64 Big Endian CFLAGS configuration
ifeq ($(ARCH),aarch64_be)
CFLAGS += -DMLK_FORCE_AARCH64_EB
endif # aarch64_be

# RISC-V 64-bit CFLAGS configuration
ifeq ($(ARCH),riscv64)
CFLAGS += -DMLK_FORCE_RISCV64
CFLAGS += -march=rv64gcv
endif # riscv64

# RISC-V 32-bit CFLAGS configuration
ifeq ($(ARCH),riscv32)
CFLAGS += -DMLK_FORCE_RISCV32
endif # riscv32

# PowerPC 64-bit Little Endian CFLAGS configuration
ifeq ($(ARCH),powerpc64le)
CFLAGS += -DMLK_FORCE_PPC64LE
endif # powerpc64le

endif # AUTO=1

endif # _AUTO_MK
