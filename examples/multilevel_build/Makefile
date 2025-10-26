# (SPDX-License-Identifier: CC-BY-4.0)

.PHONY: build run clean mlkem512_objs mlkem768_objs mlkem1024_objs mlkem_objs
.DEFAULT_GOAL := all

Q ?= @
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
MLK_SOURCE_ALL := $(wildcard \
	mlkem_native/**/*.c	  	\
	mlkem_native/**/**/*.c		\
	mlkem_native/**/**/**/*.c	\
	mlkem_native/**/**/**/**/*.c)
MLK_SOURCE:=$(foreach S,$(MLK_SOURCE_ALL),\
  $(if $(findstring /native/,$S),,$S))

BUILD_DIR=build
MLKEM512_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_DIR = $(BUILD_DIR)/mlkem1024

MLKEM512_OBJS=$(patsubst %,$(MLKEM512_DIR)/%.o,$(MLK_SOURCE))
MLKEM768_OBJS=$(patsubst %,$(MLKEM768_DIR)/%.o,$(MLK_SOURCE))
MLKEM1024_OBJS=$(patsubst %,$(MLKEM1024_DIR)/%.o,$(MLK_SOURCE))

$(MLKEM512_OBJS): $(MLKEM512_DIR)/%.c.o: %.c
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC)  -DMLK_CONFIG_MULTILEVEL_WITH_SHARED -DMLK_CONFIG_PARAMETER_SET=512 $(CFLAGS) -c $^ -o $@

$(MLKEM768_OBJS): $(MLKEM768_DIR)/%.c.o: %.c
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -DMLK_CONFIG_MULTILEVEL_NO_SHARED -DMLK_CONFIG_PARAMETER_SET=768 $(CFLAGS) -c $^ -o $@

$(MLKEM1024_OBJS): $(MLKEM1024_DIR)/%.c.o: %.c
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -DMLK_CONFIG_MULTILEVEL_NO_SHARED -DMLK_CONFIG_PARAMETER_SET=1024 $(CFLAGS) -c $^ -o $@

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
        -DMLK_CONFIG_NAMESPACE_PREFIX=mlkem \
	-std=c99 \
	-pedantic \
	-MMD \
	-O3 \
	$(CFLAGS)

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)

$(BINARY_NAME_FULL): $(APP_SOURCE) $(RNG_SOURCE) $(MLKEM512_OBJS) $(MLKEM768_OBJS) $(MLKEM1024_OBJS)
	echo "$@"
	mkdir -p $(BUILD_DIR)
	$(CC) $(CFLAGS) $^ -o $@

all: build

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
