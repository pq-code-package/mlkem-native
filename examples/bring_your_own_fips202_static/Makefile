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
	mlkem_native/src/*.c \
	mlkem_native/src/**/*.c \
	mlkem_native/src/**/**/*.c \
	mlkem_native/src/**/**/**/*.c)

INC=-Imlkem_native/

# Part B:
#
# Custom FIPS-202 implementation
FIPS202_SOURCE=custom_fips202/tiny_sha3/sha3.c

# Part C:
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

# Part D:
#
# Your application source code
APP_SOURCE=$(wildcard *.c)

ALL_SOURCE=$(MLK_SOURCE) $(FIPS202_SOURCE) $(RNG_SOURCE) $(APP_SOURCE)

#
# Configuration adjustments
#

# Pick prefix
CFLAGS += -DMLK_CONFIG_NAMESPACE_PREFIX=mlkem
# Tell mlkem-native to use serial-FIPS202 only
CFLAGS += -DMLK_CONFIG_SERIAL_FIPS202_ONLY
# Tell mlkem-native where to find the header for the custom FIPS202
CFLAGS += -DMLK_CONFIG_FIPS202_CUSTOM_HEADER="\"../custom_fips202/fips202.h\""
CFLAGS += -DMLK_CONFIG_FIPS202X4_CUSTOM_HEADER="\"../custom_fips202/fips202x4.h\""
# Add include path so we can easily include common.h from the custom FIPS202
CFLAGS += -Imlkem_native/src

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
