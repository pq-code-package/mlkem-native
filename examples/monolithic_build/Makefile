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

Q ?= @

# Part A:
#
# mlkem-native source and header files
#
# Here, we use just a single monolithic compilation unit to include
# multiple instances of mlkem-native.

MLKEM_NATIVE_SOURCE=mlkem_native_monobuild.c

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

CFLAGS := \
	-Wall \
	-Wextra \
	-Werror \
	-Wmissing-prototypes \
	-Wshadow \
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

# Set this flag to give all non-global functions internal linkage
CFLAGS += -DMLKEM_NATIVE_MONOBUILD

BIN512_FULL=$(BUILD_DIR)/$(BIN512)
BIN768_FULL=$(BUILD_DIR)/$(BIN768)
BIN1024_FULL=$(BUILD_DIR)/$(BIN1024)

LIB512_FULL=$(BUILD_DIR)/$(LIB512)
LIB768_FULL=$(BUILD_DIR)/$(LIB768)
LIB1024_FULL=$(BUILD_DIR)/$(LIB1024)

$(LIB512_FULL): $(MLKEM_NATIVE_SOURCE)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) -DMLKEM_NATIVE_CONFIG_FILE="\"config_512.h\"" $(INC) $^ -o $(BUILD_DIR)/mlkem_native512.o
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native512.o
	$(Q)strip -S $@

$(LIB768_FULL): $(MLKEM_NATIVE_SOURCE)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) -DMLKEM_NATIVE_CONFIG_FILE="\"config_768.h\"" $(INC) $^ -o $(BUILD_DIR)/mlkem_native768.o
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native768.o
	$(Q)strip -S $@

$(LIB1024_FULL): $(MLKEM_NATIVE_SOURCE)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) -DMLKEM_NATIVE_CONFIG_FILE="\"config_1024.h\"" $(INC) $^ -o $(BUILD_DIR)/mlkem_native1024.o
	$(Q)$(AR) rcs $@ $(BUILD_DIR)/mlkem_native1024.o
	$(Q)strip -S $@

$(BIN512_FULL): $(APP_SOURCE) $(LIB512_FULL)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) -DMLKEM_NATIVE_CONFIG_FILE="\"config_512.h\"" $(INC) $^ -o $@

$(BIN768_FULL): $(APP_SOURCE) $(LIB768_FULL)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) -DMLKEM_NATIVE_CONFIG_FILE="\"config_768.h\"" $(INC) $^ -o $@

$(BIN1024_FULL): $(APP_SOURCE) $(LIB1024_FULL)
	$(Q)echo "$@"
	$(Q)[ -d $(@) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) -DMLKEM_NATIVE_CONFIG_FILE="\"config_1024.h\"" $(INC) $^ -o $@

all: build

build: $(BIN512_FULL) $(BIN768_FULL) $(BIN1024_FULL)

run: $(BIN512_FULL) $(BIN768_FULL) $(BIN1024_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN512_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN768_FULL)
	$(Q)$(EXEC_WRAPPER) ./$(BIN1024_FULL)

clean:
	rm -rf $(BUILD_DIR)
