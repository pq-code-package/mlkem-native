# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean

# Part A:
#
# mlkem-native source and header files
#
# If you are not concerned about minimizing for a specific backend,
# you can just include _all_ source files into your build.
MLKEM_NATIVE_SOURCE=$(wildcard          \
	mlkem_native/*.c	  	\
	mlkem_native/*.c		\
	mlkem_native/**/*.c		\
	mlkem_native/**/**/*.c	        \
	mlkem_native/**/**/**/*.c)

INC=
INC+=-Imlkem_native/
INC+=-Imlkem_native/native

# Part B:
#
# Custom FIPS-202 implementation
FIPS202_SOURCE=custom_fips202/tiny_sha3/sha3.c

INC+=-Icustom_fips202

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

ALL_SOURCE=$(MLKEM_NATIVE_SOURCE) $(FIPS202_SOURCE) $(RNG_SOURCE) $(APP_SOURCE)

BUILD_DIR=build
BIN=test_binary

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)

$(BINARY_NAME_FULL): $(ALL_SOURCE)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) $(INC) $^ -o $@

all: run

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
