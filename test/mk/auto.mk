# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# Automatically detect system architecture and set preprocessor etc accordingly

# Native compilation
ifeq ($(CROSS_PREFIX),)
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	CFLAGS += -mavx2 -mbmi2 -mpopcnt -maes
	CFLAGS += -DMLK_FORCE_X86_64
else ifeq ($(HOST_PLATFORM),Linux-aarch64)
	CFLAGS += -DMLK_FORCE_AARCH64
else ifeq ($(HOST_PLATFORM),Darwin-arm64)
	CFLAGS += -DMLK_FORCE_AARCH64
endif
# Cross compilation
else ifneq ($(findstring aarch64_be, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64_EB
else ifneq ($(findstring aarch64, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64
else ifneq ($(findstring riscv64, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_RISCV64
else ifneq ($(findstring powerpc64le, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_PPC64LE
endif
