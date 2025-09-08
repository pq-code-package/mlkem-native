# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
ifndef _CONFIG
_CONFIG :=

SRCDIR := $(CURDIR)

##############
# GCC config #
##############

CROSS_PREFIX ?=
CC  ?= gcc
CPP ?= cpp
AR  ?= ar
CC  := $(CROSS_PREFIX)$(CC)
CPP := $(CROSS_PREFIX)$(CPP)
AR  := $(CROSS_PREFIX)$(AR)
LD  := $(CC)
OBJCOPY := $(CROSS_PREFIX)objcopy
SIZE := $(CROSS_PREFIX)size

# NOTE: gcc-ar is a wrapper around ar that ensures proper integration with GCC plugins,
# 	such as lto. Using gcc-ar is preferred when creating or linking static libraries
# 	if the binary is compiled with -flto. However, it is not universally present, so
#       only use it if available.
CC_AR ?= $(if $(and $(findstring gcc,$(shell $(CC) --version)), $(findstring gcc-ar, $(shell which $(CROSS_PREFIX)gcc-ar))),gcc-ar,ar)
CC_AR  := $(CROSS_PREFIX)$(CC_AR)

#################
# Common config #
#################
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
	-Wno-long-long \
	-Wno-unknown-pragmas \
	-Wno-unused-command-line-argument \
	-O3 \
	-fomit-frame-pointer \
	-std=c99 \
	-pedantic \
	-MMD \
	$(CFLAGS)

##################
# Some Variables #
##################
Q ?= @

HOST_PLATFORM := $(shell uname -s)-$(shell uname -m)
# linux x86_64
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	CFLAGS += -z noexecstack
endif


ifeq ($(CYCLES),PMU)
	CFLAGS += -DPMU_CYCLES
endif

ifeq ($(CYCLES),PERF)
	CFLAGS += -DPERF_CYCLES
endif

ifeq ($(CYCLES),MAC)
	CFLAGS += -DMAC_CYCLES
endif

##########################
# Architecture Detection #
##########################

# Check if we're building for AArch64 (native or cross-compilation)
IS_AARCH64 := 0
ifeq ($(CROSS_PREFIX),)
# Native compilation - check HOST_PLATFORM
ifeq ($(HOST_PLATFORM),Linux-aarch64)
	IS_AARCH64 := 1
else ifeq ($(HOST_PLATFORM),Darwin-arm64)
	IS_AARCH64 := 1
endif
else
# Cross compilation - check CROSS_PREFIX for aarch64- (not aarch64_be-)
ifneq ($(findstring aarch64-, $(CROSS_PREFIX)),)
	IS_AARCH64 := 1
endif
endif

# Check if we're building for x86_64 (native or cross-compilation)
IS_X86_64 := 0
ifeq ($(CROSS_PREFIX),)
# Native compilation - check HOST_PLATFORM
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	IS_X86_64 := 1
else ifeq ($(HOST_PLATFORM),Darwin-x86_64)
	IS_X86_64 := 1
endif
else
# Cross compilation - check CROSS_PREFIX for x86_64-
ifneq ($(findstring x86_64-, $(CROSS_PREFIX)),)
	IS_X86_64 := 1
endif
endif

##############################
# Include retained variables #
##############################

AUTO ?= 1
CYCLES ?=
OPT ?= 1
RETAINED_VARS := CROSS_PREFIX CYCLES OPT AUTO

BUILD_DIR ?= test/build

MAKE_OBJS = $(2:%=$(1)/%.o)
OBJS = $(call MAKE_OBJS,$(BUILD_DIR),$(1))

CONFIG := $(BUILD_DIR)/config.mk

-include $(CONFIG)

$(CONFIG):
	@echo "  GEN     $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	@echo "# These variables are retained and can't be changed without a clean" > $@
	@$(foreach var,$(RETAINED_VARS),echo "$(var) := $($(var))" >> $@; echo "LAST_$(var) := $($(var))" >> $@;)

define VAR_CHECK
ifneq ($$(origin LAST_$(1)),undefined)
ifneq "$$($(1))" "$$(LAST_$(1))"
$$(info Variable $(1) changed, forcing rebuild!)
.PHONY: $(CONFIG)
endif
endif
endef

$(foreach VAR,$(RETAINED_VARS),$(eval $(call VAR_CHECK,$(VAR))))
endif
