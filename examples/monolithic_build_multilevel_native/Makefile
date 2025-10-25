# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

.PHONY: build run clean size
.DEFAULT_GOAL := all

# Append cross-prefix for cross compilation
# Remove or ignore for native builds
CC  ?= gcc
AR  ?= ar
SIZE ?= size
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

ifeq (,$(findstring $(CROSS_PREFIX),$(AR)))
AR  := $(CROSS_PREFIX)$(AR)
endif

ifeq (,$(findstring $(CROSS_PREFIX),$(SIZE)))
SIZE  := $(CROSS_PREFIX)$(SIZE)
endif

# Part A:
#
# mlkem-native source and header files
#
# Here, the mlkem-native C source is directly included in main.c.
MLK_SOURCE_ASM = mlkem/mlkem_native.S

INC=-Imlkem/ -Imlkem/src/ -I./

# Part B:
#
# Random number generator
#
# !!! WARNING !!!
#
# The randombytes() implementation used here is for TESTING ONLY.
# You MUST NOT use this implementation outside of testing.
#
# !!! WARNING !!!
RNG_SOURCE=$(wildcard test_only_rng/*.c)

# Part C:
#
# Your application source code
APP_SOURCE=$(RNG_SOURCE) main.c

BUILD_DIR=build
BIN=test_binary

# Automatically detect system architecture and set preprocessor etc accordingly
HOST_PLATFORM := $(shell uname -s)-$(shell uname -m)

# linux x86_64
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	CFLAGS += -z noexecstack
endif

# Native compilation
ifeq ($(CROSS_PREFIX),)
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	CFLAGS += -mavx2 -mbmi2
	CFLAGS += -DMLK_FORCE_X86_64
else ifeq ($(HOST_PLATFORM),Linux-aarch64)
	CFLAGS += -DMLK_FORCE_AARCH64
else ifeq ($(HOST_PLATFORM),Darwin-arm64)
	CFLAGS += -DMLK_FORCE_AARCH64
endif
# Cross compilation
else ifneq ($(findstring x86_64, $(CROSS_PREFIX)),)
	CFLAGS += -mavx2 -mbmi2
	CFLAGS += -DMLK_FORCE_X86_64
else ifneq ($(findstring aarch64_be, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64_EB
else ifneq ($(findstring aarch64, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64
else ifneq ($(findstring riscv64, $(CROSS_PREFIX)),)
	CFLAGS += -march=rv64gcv
	CFLAGS += -DMLK_FORCE_RISCV64
else ifneq ($(findstring riscv32, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_RISCV32
else ifneq ($(findstring powerpc64le, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_PPC64LE
endif

CFLAGS := \
	-Wall \
	-Wextra \
	-Werror \
	-Wmissing-prototypes \
	-Wshadow \
	-Wpointer-arith \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wredundant-decls \
	-Wconversion \
	-Wsign-conversion \
	-Wno-unused-command-line-argument \
	-fomit-frame-pointer \
	-std=c99 \
	-pedantic \
	-MMD \
	-O3 \
	$(CFLAGS)

ASMFLAGS = -DMLK_CONFIG_FILE=\"multilevel_config.h\"
ASMFLAGS += -DMLK_CONFIG_MULTILEVEL_WITH_SHARED

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)

MLK_OBJ_C=$(patsubst %,$(BUILD_DIR)/%.o,$(MLK_SOURCE_C))
MLK_OBJ_ASM=$(patsubst %,$(BUILD_DIR)/%.o,$(MLK_SOURCE_ASM))

Q ?= @

$(BUILD_DIR)/%.c.o: %.c
	$(Q)echo "CC  $^"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) $(INC) $^ -o $@

$(BUILD_DIR)/%.S.o: %.S
	$(Q)echo "AS  $^"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) $(ASMFLAGS) $(INC) $^ -o $@

$(BINARY_NAME_FULL): $(APP_SOURCE) $(MLK_OBJ_ASM)
	$(Q)echo "CC  $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) $(INC) $^ -o $@
	$(Q)strip -S $@

all: build size

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

size: build
	$(Q)echo "=== Size info for binaries $(BINARY_NAME_FULL)==="
	$(Q)$(SIZE) $(BINARY_NAME_FULL)
	$(Q)echo " "


clean:
	rm -rf $(BUILD_DIR)
