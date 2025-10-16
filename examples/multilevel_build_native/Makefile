# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean mlkem512_objs mlkem768_objs mlkem1024_objs mlkem_objs size size_objs
.DEFAULT_GOAL := all

Q ?= @
# Append cross-prefix for cross compilation
# Remove or ignore for native builds
CC  ?= gcc
SIZE ?= size
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

ifeq (,$(findstring $(CROSS_PREFIX),$(SIZE)))
SIZE  := $(CROSS_PREFIX)$(SIZE)
endif

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
	-Werror \
	-Wpointer-arith \
	-Wredundant-decls \
	-Wconversion \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-fomit-frame-pointer \
	-DMLK_CONFIG_NAMESPACE_PREFIX=mlkem \
	-std=c99 \
	-pedantic \
	-MMD \
	-O3 \
	$(CFLAGS)


# Part A:
#
# mlkem-native source and header files
#
# If you are not concerned about minimizing for a specific backend,
# you can just include _all_ source files into your build.
MLK_SOURCE := $(wildcard \
	mlkem_native/mlkem/src/*.c             \
	mlkem_native/mlkem/src/**/*.c          \
	mlkem_native/mlkem/src/**/**/*.c       \
	mlkem_native/mlkem/src/**/**/**/*.c    \
	mlkem_native/mlkem/src/**/**/**/**/*.c \
	mlkem_native/mlkem/src/*.S             \
	mlkem_native/mlkem/src/**/*.S          \
	mlkem_native/mlkem/src/**/**/*.S       \
	mlkem_native/mlkem/src/**/**/**/*.S    \
	mlkem_native/mlkem/src/**/**/**/**/*.S)

BUILD_DIR=build
MLKEM512_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_DIR = $(BUILD_DIR)/mlkem1024

MLKEM512_OBJS=$(patsubst %,$(MLKEM512_DIR)/%.o,$(MLK_SOURCE))
MLKEM768_OBJS=$(patsubst %,$(MLKEM768_DIR)/%.o,$(MLK_SOURCE))
MLKEM1024_OBJS=$(patsubst %,$(MLKEM1024_DIR)/%.o,$(MLK_SOURCE))

$(MLKEM512_OBJS): $(MLKEM512_DIR)/%.o: %
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 -DMLK_CONFIG_MULTILEVEL_WITH_SHARED -DMLK_CONFIG_PARAMETER_SET=512 $(CFLAGS) -c $^ -o $@

$(MLKEM768_OBJS): $(MLKEM768_DIR)/%.o: %
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 -DMLK_CONFIG_MULTILEVEL_NO_SHARED -DMLK_CONFIG_PARAMETER_SET=768 $(CFLAGS) -c $^ -o $@

$(MLKEM1024_OBJS): $(MLKEM1024_DIR)/%.o: %
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 -DMLK_CONFIG_MULTILEVEL_NO_SHARED -DMLK_CONFIG_PARAMETER_SET=1024 $(CFLAGS) -c $^ -o $@

mlkem512_objs: $(MLKEM512_OBJS)
mlkem768_objs: $(MLKEM768_OBJS)
mlkem1024_objs: $(MLKEM1024_OBJS)
mlkem_objs: mlkem512_objs mlkem768_objs mlkem1024_objs

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
APP_SOURCE=$(wildcard *.c)

BIN=test_binary
BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)

$(BINARY_NAME_FULL): $(APP_SOURCE) $(RNG_SOURCE) $(MLKEM512_OBJS) $(MLKEM768_OBJS) $(MLKEM1024_OBJS)
	$(Q)mkdir -p $(BUILD_DIR)
	$(Q)$(CC) $(CFLAGS) $^ -o $@

all: build size_objs

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

size: build
	@echo "=== Size info for $(BINARY_NAME_FULL) ==="
	$(Q)$(SIZE) $(BINARY_NAME_FULL)

size_objs: size
	$(Q)echo "=== Object size summary ==="
	$(Q)$(SIZE) $(shell find $(BUILD_DIR)/mlkem512 -name '*.o') | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)
	$(Q)$(SIZE) $(shell find $(BUILD_DIR)/mlkem768 -name '*.o') | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)
	$(Q)$(SIZE) $(shell find $(BUILD_DIR)/mlkem1024 -name '*.o') | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)

clean:
	rm -rf $(BUILD_DIR)
