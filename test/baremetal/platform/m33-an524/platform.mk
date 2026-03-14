# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

PLATFORM_PATH:=test/baremetal/platform/m33-an524

CROSS_PREFIX=arm-none-eabi-
CC=gcc

# Use PMU cycle counting by default
CYCLES ?= PMU

# Reduce iterations for benchmarking and functional tests
CFLAGS += -DMLK_BENCHMARK_NTESTS=10 -DMLK_BENCHMARK_NITERATIONS=10 -DMLK_BENCHMARK_NWARMUP=10
CFLAGS += -DNTESTS_FUNC=100


CFLAGS += -DMLK_BUMP_ALLOC_SIZE=65536
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
	--sysroot=$(SYSROOT) \
	-DDEVICE=an524 \
	-I$(M33_AN524_PATH) \
	-I$(M33_AN524_PATH)/m-profile \
	-DARMCM33 \
	-DSEMIHOSTING \
	-DCMDLINE_BASE_ADDR=0x20007000

ARCH_FLAGS += \
	-mcpu=cortex-m33 \
	-mthumb \
	-mfloat-abi=soft

CFLAGS += \
	$(ARCH_FLAGS) \
	--specs=nosys.specs

CFLAGS += $(CFLAGS_EXTRA)

LDSCRIPT = $(M33_AN524_PATH)/m33-an524.ld

LDFLAGS += \
	-Wl,--gc-sections \
	-Wl,--no-warn-rwx-segments \
	-L.

LDFLAGS += \
	--specs=nosys.specs \
	-Wl,--wrap=_open \
	-Wl,--wrap=_close \
	-Wl,--wrap=_read \
	-Wl,--wrap=_write \
	-Wl,--wrap=_fstat \
	-Wl,--wrap=_getpid \
	-Wl,--wrap=_isatty \
	-Wl,--wrap=_kill \
	-Wl,--wrap=_lseek \
	-Wl,--wrap=main \
	-ffreestanding \
	-T$(LDSCRIPT) \
	$(ARCH_FLAGS)

# Extra sources to be included in test binaries
EXTRA_SOURCES = $(wildcard $(M33_AN524_PATH)/*.c)
# The CMSIS files fail compilation if conversion warnings are enabled
EXTRA_SOURCES_CFLAGS = -Wno-conversion -Wno-sign-conversion

EXEC_WRAPPER := $(realpath $(PLATFORM_PATH)/exec_wrapper.py)
