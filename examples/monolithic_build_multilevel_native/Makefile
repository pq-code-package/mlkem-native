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
# multiple instances of mlkem-native, plus all assembly.

MLKEM_NATIVE_SOURCE_C=mlkem_native_all.c
MLKEM_NATIVE_SOURCE_ASM = $(wildcard \
	mlkem/**/*.S                 \
	mlkem/**/**/*.S              \
	mlkem/**/**/**/*.S           \
	mlkem/**/**/**/**/*.S        \
	mlkem/**/**/**/**/**/*.S)

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

ASMFLAGS = -DMLKEM_NATIVE_CONFIG_FILE=\"multilevel_config.h\"
ASMFLAGS += -DMLKEM_NATIVE_MULTILEVEL_BUILD_WITH_SHARED

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)
LIB_NAME_FULL=$(BUILD_DIR)/$(LIB)

MLKEM_NATIVE_OBJ_C=$(patsubst %,$(BUILD_DIR)/%.o,$(MLKEM_NATIVE_SOURCE_C))
MLKEM_NATIVE_OBJ_ASM=$(patsubst %,$(BUILD_DIR)/%.o,$(MLKEM_NATIVE_SOURCE_ASM))

Q ?= @

$(BUILD_DIR)/%.c.o: %.c
	$(Q)echo "CC  $^"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) $(INC) $^ -o $@

$(BUILD_DIR)/%.S.o: %.S
	$(Q)echo "AS  $^"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) $(ASMFLAGS) $(INC) $^ -o $@

$(LIB_NAME_FULL): $(MLKEM_NATIVE_OBJ_C) $(MLKEM_NATIVE_OBJ_ASM)
	$(Q)echo "AR  $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(AR) rcs $@ $^
	$(Q)strip -S $@

$(BINARY_NAME_FULL): $(APP_SOURCE) $(LIB_NAME_FULL)
	$(Q)echo "CC  $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) $(INC) $^ -o $@

all: build

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
