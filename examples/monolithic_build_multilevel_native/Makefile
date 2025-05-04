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
# Here, the mlkem-native C source is directly included in main.c.
MLK_SOURCE_ASM = $(wildcard \
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

# Automatically detect system architecture and set preprocessor etc accordingly
HOST_PLATFORM := $(shell uname -s)-$(shell uname -m)
# linux x86_64
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	CFLAGS += -z noexecstack
endif

ifeq ($(HOST_PLATFORM),Linux-x86_64)
ifeq ($(CROSS_PREFIX),)
	CFLAGS += -mavx2 -mbmi2 -mpopcnt -maes
	CFLAGS += -DMLK_FORCE_X86_64
else ifneq ($(findstring aarch64_be, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64_EB
else ifneq ($(findstring aarch64, $(CROSS_PREFIX)),)
	CFLAGS += -DMLK_FORCE_AARCH64
else

endif

# linux aarch64
else ifeq ($(HOST_PLATFORM),Linux-aarch64)
ifeq ($(CROSS_PREFIX),)
	CFLAGS += -DMLK_FORCE_AARCH64
else ifneq ($(findstring x86_64, $(CROSS_PREFIX)),)
	CFLAGS += -mavx2 -mbmi2 -mpopcnt -maes
	CFLAGS += -DMLK_FORCE_X86_64
else
endif

# darwin aarch64
else ifeq ($(HOST_PLATFORM),Darwin-arm64)
	CFLAGS += -DMLK_FORCE_AARCH64
endif

CFLAGS := \
	-Wall \
	-Wextra \
	-Werror \
	-Wmissing-prototypes \
	-Wshadow \
	-Wpointer-arith \
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-function \
	-Wredundant-decls \
	-Wno-unused-command-line-argument \
	-fomit-frame-pointer \
	-std=c99 \
	-pedantic \
	-MMD \
	-O3 \
	$(CFLAGS)

ASMFLAGS = -DMLK_CONFIG_FILE=\"multilevel_config.h\"
ASMFLAGS += -DMLK_CONFIG_MULTILEVEL_WITH_SHARED

BINARY_NAME_FULL=$(BUILD_DIR)/$(BIN)

MLK_OBJ_C=$(patsubst %,$(BUILD_DIR)/%.o,$(MLK_SOURCE_C))
MLK_OBJ_ASM=$(patsubst %,$(BUILD_DIR)/%.o,$(MLK_SOURCE_ASM))

Q ?= @

$(BUILD_DIR)/%.c.o: %.c
	$(Q)echo "CC  $^"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) $(INC) $^ -o $@

$(BUILD_DIR)/%.S.o: %.S
	$(Q)echo "AS  $^"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c $(CFLAGS) $(ASMFLAGS) $(INC) $^ -o $@

$(BINARY_NAME_FULL): $(APP_SOURCE) $(MLK_OBJ_ASM)
	$(Q)echo "CC  $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) $(INC) $^ -o $@
	$(Q)strip -S $@

all: build

build: $(BINARY_NAME_FULL)

run: $(BINARY_NAME_FULL)
	$(EXEC_WRAPPER) ./$(BINARY_NAME_FULL)

clean:
	rm -rf $(BUILD_DIR)
