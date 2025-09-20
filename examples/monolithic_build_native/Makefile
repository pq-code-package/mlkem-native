# (SPDX-License-Identifier: CC-BY-4.0)

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

Q ?= @
# Part A:
#
# mlkem-native source and header files
#
# Here, we use just a single monolithic compilation unit to include
# multiple instances of mlkem-native.

MLK_SOURCE=mlkem/mlkem_native.c mlkem/mlkem_native.S

INC=-Imlkem/ -I./

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
BIN512=test_binary_mlkem512
BIN768=test_binary_mlkem768
BIN1024=test_binary_mlkem1024
LIB512=libmlkem512.a
LIB768=libmlkem768.a
LIB1024=libmlkem1024.a

MLK_OBJS=$(BUILD_DIR)/mlkem_native.c.o $(BUILD_DIR)/mlkem_native.S.o

# Automatically detect system architecture and set preprocessor etc accordingly
HOST_PLATFORM := $(shell uname -s)-$(shell uname -m)

# linux x86_64
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	CFLAGS += -z noexecstack
endif

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
else ifneq ($(findstring x86_64, $(CROSS_PREFIX)),)
	CFLAGS += -mavx2 -mbmi2 -mpopcnt -maes
	CFLAGS += -DMLK_FORCE_X86_64
else ifneq ($(findstring aarch64_be, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64_EB
else ifneq ($(findstring aarch64, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64
else ifneq ($(findstring riscv64, $(CROSS_PREFIX)),)
	CFLAGS += -march=rv64gcv_zvl256b
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
	-Wredundant-decls \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-fomit-frame-pointer \
	-std=c99 \
	-pedantic \
	-MMD \
	-O3 \
        -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH \
        -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 \
        $(CFLAGS)

BIN512_FULL=$(BUILD_DIR)/$(BIN512)
BIN768_FULL=$(BUILD_DIR)/$(BIN768)
BIN1024_FULL=$(BUILD_DIR)/$(BIN1024)

LIB512_FULL=$(BUILD_DIR)/$(LIB512)
LIB768_FULL=$(BUILD_DIR)/$(LIB768)
LIB1024_FULL=$(BUILD_DIR)/$(LIB1024)

$(LIB512_FULL): $(MLK_SOURCE)
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)echo "$(BUILD_DIR)/mlkem_native512.c.o"
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_512.h\"" $(INC) mlkem/mlkem_native.c -o $(BUILD_DIR)/mlkem_native512.c.o
	$(Q)echo "$(BUILD_DIR)/mlkem_native512.S.o"
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_512.h\"" $(INC) mlkem/mlkem_native.S -o $(BUILD_DIR)/mlkem_native512.S.o
	$(Q)echo "$@"
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native512.c.o $(BUILD_DIR)/mlkem_native512.S.o
	$(Q)strip -S $@

$(LIB768_FULL): $(MLK_SOURCE)
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)echo "$(BUILD_DIR)/mlkem_native768.c.o"
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_768.h\"" $(INC) mlkem/mlkem_native.c -o $(BUILD_DIR)/mlkem_native768.c.o
	$(Q)echo "$(BUILD_DIR)/mlkem_native768.S.o"
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_768.h\"" $(INC) mlkem/mlkem_native.S -o $(BUILD_DIR)/mlkem_native768.S.o
	$(Q)echo "$@"
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native768.c.o $(BUILD_DIR)/mlkem_native768.S.o
	$(Q)strip -S $@

$(LIB1024_FULL): $(MLK_SOURCE)
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)echo "$(BUILD_DIR)/mlkem_native1024.c.o"
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_1024.h\"" $(INC) mlkem/mlkem_native.c -o $(BUILD_DIR)/mlkem_native1024.c.o
	$(Q)echo "$(BUILD_DIR)/mlkem_native1024.S.o"
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_1024.h\"" $(INC) mlkem/mlkem_native.S -o $(BUILD_DIR)/mlkem_native1024.S.o
	$(Q)echo "$@"
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native1024.c.o $(BUILD_DIR)/mlkem_native1024.S.o
	$(Q)strip -S $@

$(BIN512_FULL): $(APP_SOURCE) $(LIB512_FULL)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) -DMLK_CONFIG_API_PARAMETER_SET=512 $(INC) $^ -o $@

$(BIN768_FULL): $(APP_SOURCE) $(LIB768_FULL)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) -DMLK_CONFIG_API_PARAMETER_SET=768 $(INC) $^ -o $@

$(BIN1024_FULL): $(APP_SOURCE) $(LIB1024_FULL)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) -DMLK_CONFIG_API_PARAMETER_SET=1024 $(INC) $^ -o $@

all: build size

build: $(BIN512_FULL) $(BIN768_FULL) $(BIN1024_FULL)

run: $(BIN512_FULL) $(BIN768_FULL) $(BIN1024_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN512_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN768_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN1024_FULL)

size: build
	@echo "=== Size info for static libs ==="
	$(Q)$(SIZE) $(LIB512_FULL) | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)
	$(Q)$(SIZE) $(LIB768_FULL) | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)
	$(Q)$(SIZE) $(LIB1024_FULL) | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)

clean:
	rm -rf $(BUILD_DIR)
