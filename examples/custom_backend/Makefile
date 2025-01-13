# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean
.DEFAULT_GOAL := all

# Append cross-prefix for cross compilation
# Remove or ignore for native builds
CC  ?= gcc
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

# Part A:
#
# mlkem-native source and header files
#
# If you are not concerned about minimizing for a specific backend,
# you can just include _all_ source files into your build.
MLKEM_NATIVE_SOURCE=$(wildcard          \
    mlkem_native/**/*.c                 \
    mlkem_native/**/**/*.c              \
    mlkem_native/**/**/**/*.c           \
    mlkem_native/**/**/**/**/*.c        \
    mlkem_native/**/**/**/**/**/*.c)

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

ALL_SOURCE=$(MLKEM_NATIVE_SOURCE) $(RNG_SOURCE) $(APP_SOURCE)

BUILD_DIR=build
BIN=test_binary

CFLAGS := \
	-Wall \
	-Wextra \
	-Werror \
	-Wmissing-prototypes \
	-Wshadow \
	-Werror \
	-Wpointer-arith \
	-Wredundant-decls \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-fomit-frame-pointer \
	-std=c99 \
	-pedantic \
	-MMD \
	$(CFLAGS)

CFLAGS+=-DMLKEM_NATIVE_CONFIG_FILE="\"custom_config.h\""

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)

$(BINARY_NAME_FULL): $(ALL_SOURCE)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) $(CFLAGS) $(INC) $^ -o $@

all: build

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
