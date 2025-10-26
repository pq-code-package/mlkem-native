# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

.PHONY: build run clean
.DEFAULT_GOAL := all

CC  ?= gcc
AR  ?= ar

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

# If you want to use the native backends, the compiler needs to know about
# the target architecture. Here, we import the default host detection from
# mlkem-native's tests, but you can write your own or specialize accordingly.
AUTO ?= 1
include auto.mk

# The following only concerns the cross-compilation tests.
# You can likely ignore the following for your application.
#
# Append cross-prefix for cross compilation
# When called from the root Makefile, CROSS_PREFIX has already been added here
ifeq (,$(findstring $(CROSS_PREFIX),$(CC)))
CC  := $(CROSS_PREFIX)$(CC)
endif

ifeq (,$(findstring $(CROSS_PREFIX),$(AR)))
AR  := $(CROSS_PREFIX)$(AR)
endif

Q ?= @

# Part A:
#
# mlkem-native source and header files
#
# Here, we use just a single C and assembly unit.

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

BIN512_FULL=$(BUILD_DIR)/$(BIN512)
BIN768_FULL=$(BUILD_DIR)/$(BIN768)
BIN1024_FULL=$(BUILD_DIR)/$(BIN1024)

LIB512_FULL=$(BUILD_DIR)/$(LIB512)
LIB768_FULL=$(BUILD_DIR)/$(LIB768)
LIB1024_FULL=$(BUILD_DIR)/$(LIB1024)

$(LIB512_FULL): $(MLK_SOURCE)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_512.h\"" $(INC) mlkem/mlkem_native.c -o $(BUILD_DIR)/mlkem_native512.c.o
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_512.h\"" $(INC) mlkem/mlkem_native.S -o $(BUILD_DIR)/mlkem_native512.S.o
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native512.c.o $(BUILD_DIR)/mlkem_native512.S.o
	$(Q)strip -S $@

$(LIB768_FULL): $(MLK_SOURCE)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_768.h\"" $(INC) mlkem/mlkem_native.c -o $(BUILD_DIR)/mlkem_native768.c.o
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_768.h\"" $(INC) mlkem/mlkem_native.S -o $(BUILD_DIR)/mlkem_native768.S.o
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native768.c.o $(BUILD_DIR)/mlkem_native768.S.o
	$(Q)strip -S $@

$(LIB1024_FULL): $(MLK_SOURCE)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_1024.h\"" $(INC) mlkem/mlkem_native.c -o $(BUILD_DIR)/mlkem_native1024.c.o
	$(Q)$(CC) -c $(CFLAGS) -DMLK_CONFIG_FILE="\"config_1024.h\"" $(INC) mlkem/mlkem_native.S -o $(BUILD_DIR)/mlkem_native1024.S.o
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

all: build

build: $(BIN512_FULL) $(BIN768_FULL) $(BIN1024_FULL)

run: $(BIN512_FULL) $(BIN768_FULL) $(BIN1024_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN512_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN768_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN1024_FULL)

clean:
	rm -rf $(BUILD_DIR)
