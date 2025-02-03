# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean
.DEFAULT_GOAL := all

# Append cross-prefix for cross compilation
# Remove or ignore for native builds
CC  ?= gcc
AR  ?= ar
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

ifeq (,$(findstring $(CROSS_PREFIX),$(AR)))
AR  := $(CROSS_PREFIX)$(AR)
endif

# Part A:
#
# mlkem-native source and header files
#
# Here, we use just a single monolithic compilation unit to include
# multiple instances of mlkem-native.

MLKEM_NATIVE_SOURCE=mlkem_native_all.c

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
BIN=test_binary
LIB=libmlkem.a

CFLAGS := \
	-Wall \
	-Wextra \
	-Wmissing-prototypes \
	-Wshadow \
	-Wpointer-arith \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-fomit-frame-pointer \
	-std=c99 \
	-pedantic \
	-MMD \
	-O3 \
	$(CFLAGS)

# Set this flag to give all non-global functions internal linkage
CFLAGS += -DMLKEM_NATIVE_MONOBUILD

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)
LIB_NAME_FULL=$(BUILD_DIR)/$(LIB)

$(LIB_NAME_FULL): $(MLKEM_NATIVE_SOURCE)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) -c $(CFLAGS) $(INC) $^ -o $(BUILD_DIR)/mlkem_native.o
	$(AR) rcs $@ $(BUILD_DIR)/mlkem_native.o
	strip -S $@

$(BINARY_NAME_FULL): $(APP_SOURCE) $(LIB_NAME_FULL)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) $(CFLAGS) $(INC) $^ -o $@

all: build

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
