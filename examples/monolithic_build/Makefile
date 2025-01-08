# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean

# Part A:
#
# mlkem-native source and header files
#
# If you are not concerned about minimizing for a specific backend,
# you can just include _all_ source files into your build.

INC=
INC+=-I./
INC+=-Imlkem/
INC+=-Imlkem/native
INC+=-Imlkem/fips202
INC+=-Imlkem/fips202/native

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
APP_SOURCE=main.c mlkem_native_all.c

ALL_SOURCE=$(MLKEM_NATIVE_SOURCE) $(RNG_SOURCE) $(APP_SOURCE)

BUILD_DIR=build
BIN=test_binary

CFLAGS := \
	-Wall \
	-Wextra \
	-Wmissing-prototypes \
	-Wshadow \
	-Wpointer-arith \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-O3 \
	-fomit-frame-pointer \
	-std=c90 \
	-pedantic \
	-MMD
# Set this flag to give all non-global functions internal linkage
CFLAGS += -DMLKEM_NATIVE_MONOBUILD

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)

$(BINARY_NAME_FULL): $(ALL_SOURCE)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) $(CFLAGS) $(INC) $^ -o $@

all: run

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
