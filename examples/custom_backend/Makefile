# (SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT)

.PHONY: build run clean
.DEFAULT_GOAL := all

CC  ?= gcc

# Adjust CFLAGS if needed
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
	-std=c99 \
	-pedantic \
	-MMD \
	$(CFLAGS)

# The following only concerns the cross-compilation tests.
# You can likely ignore the following for your application.
#
# Append cross-prefix for cross compilation
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

# Part A:
#
# mlkem-native source and header files
#
# In this example, we compile the individual mlkem-native source files directly.
# Alternatively, you can compile the 'monobuild' source file mlkem_native.c.
# See examples/monolithic_build for that.
MLK_SOURCE=$(wildcard \
    mlkem_native/mlkem/src/*.c \
    mlkem_native/mlkem/src/**/*.c \
    mlkem_native/mlkem/src/**/**/*.c \
    mlkem_native/mlkem/src/**/**/**/*.c \
    mlkem_native/mlkem/src/**/**/**/**/*.c)

INC=-Imlkem_native -Imlkem_native/mlkem

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

ALL_SOURCE=$(MLK_SOURCE) $(RNG_SOURCE) $(APP_SOURCE)


#
# Configuration adjustments
#

# Pick custom config file
CFLAGS+=-DMLK_CONFIG_FILE="\"custom_config.h\""

BUILD_DIR=build
BIN=test_binary

BINARY_NAME_FULL_512=$(BUILD_DIR)/$(BIN)512
BINARY_NAME_FULL_768=$(BUILD_DIR)/$(BIN)768
BINARY_NAME_FULL_1024=$(BUILD_DIR)/$(BIN)1024
BINARIES_FULL=$(BINARY_NAME_FULL_512) $(BINARY_NAME_FULL_768) $(BINARY_NAME_FULL_1024)

$(BINARY_NAME_FULL_512): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512
$(BINARY_NAME_FULL_768): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768
$(BINARY_NAME_FULL_1024): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024

$(BINARIES_FULL): $(ALL_SOURCE)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) $(CFLAGS) $(INC) $^ -o $@

all: build

build: $(BINARIES_FULL)

run: $(BINARIES_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_512)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_768)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_1024)

clean:
	rm -rf $(BUILD_DIR)
