# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

PLATFORM_PATH:=test/baremetal/platform/aarch64-virt

CROSS_PREFIX=aarch64-none-elf-
CC=gcc

# Reduce iterations -- bare-metal semihosting I/O is slow
CFLAGS += -DNTESTS=3 -DMLK_TEST_NO_UNALIGNED

CFLAGS += \
	-O3 \
	-Wall -Wextra -Wshadow \
	-Wno-pedantic \
	-Wno-redundant-decls \
	-Wno-missing-prototypes \
	-Wno-conversion \
	-Wno-sign-conversion \
	-fno-common \
	-ffunction-sections \
	-fdata-sections \
	-mstrict-align \
	-ffreestanding \
	-DSEMIHOSTING

CFLAGS += $(CFLAGS_EXTRA)

LDSCRIPT = $(PLATFORM_PATH)/virt.ld

LDFLAGS += \
	-nostdlib \
	-static \
	-Wl,--gc-sections \
	-Wl,--no-warn-rwx-segments \
	-T$(LDSCRIPT)

LDLIBS += -lgcc

# Extra sources to be included in test binaries
EXTRA_SOURCES = $(wildcard $(PLATFORM_PATH)/*.c) $(wildcard $(PLATFORM_PATH)/*.S)
# Suppress warnings for platform support code
EXTRA_SOURCES_CFLAGS = -Wno-conversion -Wno-sign-conversion

EXEC_WRAPPER := $(realpath $(PLATFORM_PATH)/exec_wrapper.py)
