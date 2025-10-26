# (SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT)

.PHONY: build run clean mlkem512_objs mlkem768_objs mlkem1024_objs mlkem_objs
.DEFAULT_GOAL := all

Q ?= @

CC  ?= gcc

# The following only concerns the cross-compilation tests.
# You can likely ignore the following for your application.
#
# Append cross-prefix for cross compilation
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

CFLAGS := \
	-Wall \
	-Wextra \
	-Werror=unused-result \
	-Wpedantic \
	-Werror \
	-Wmissing-prototypes \
	-Wshadow \
	-Wpointer-arith \
	-Wredundant-decls \
	-Wconversion \
	-Wsign-conversion \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-O3 \
	-fomit-frame-pointer \
	-DMLK_CONFIG_NAMESPACE_PREFIX=mlkem \
	-std=c99 \
	-pedantic \
	-MMD \
	$(CFLAGS)


# Part A:
#
# mlkem-native source and header files
#
# In this example, we compile the individual mlkem-native source files directly.
# Alternatively, you can compile the 'monobuild' source file mlkem_native.c.
# See examples/monolithic_build for that.
MLK_SOURCE := $(wildcard \
	mlkem_native/mlkem/src/*.c \
	mlkem_native/mlkem/src/**/*.c \
	mlkem_native/mlkem/src/**/**/*.c \
	mlkem_native/mlkem/src/**/**/**/*.c \
	mlkem_native/mlkem/src/**/**/**/**/*.c \
	mlkem_native/mlkem/src/*.S \
	mlkem_native/mlkem/src/**/*.S \
	mlkem_native/mlkem/src/**/**/*.S \
	mlkem_native/mlkem/src/**/**/**/*.S \
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

all: build

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
