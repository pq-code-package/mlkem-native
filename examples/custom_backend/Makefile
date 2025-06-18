# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean size
.DEFAULT_GOAL := all

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

# Part A:
#
# mlkem-native source and header files
#
# If you are not concerned about minimizing for a specific backend,
# you can just include _all_ source files into your build.
MLK_SOURCE=$(wildcard                   \
    mlkem_native/**/**/*.c              \
    mlkem_native/**/**/**/*.c           \
    mlkem_native/**/**/**/**/*.c        \
    mlkem_native/**/**/**/**/**/*.c     \
	mlkem_native/**/**/**/**/**/**/*.c)

INC=-Imlkem_native -Imlkem_native/mlkem -Imlkem_native/mlkem/src

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
	-O3 \
	$(CFLAGS)

CFLAGS+=-DMLK_CONFIG_FILE="\"custom_config.h\""

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

all: build size

build: $(BINARIES_FULL)

run: $(BINARIES_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_512)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_768)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL_1024)

size: build
	@echo "=== Size info for binaries $(BINARY_NAME_FULL_512) ==="
	@$(SIZE) $(BINARY_NAME_FULL_512)
	@echo "=== Size info for binaries $(BINARY_NAME_FULL_768) ==="
	@$(SIZE) $(BINARY_NAME_FULL_768)
	@echo "=== Size info for binaries $(BINARY_NAME_FULL_1024) ==="
	@$(SIZE) $(BINARY_NAME_FULL_1024)

clean:
	rm -rf $(BUILD_DIR)
