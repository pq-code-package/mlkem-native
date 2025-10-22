# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

PLATFORM_PATH:=test/baremetal/platform/avr

CROSS_PREFIX=avr-
CC=gcc

# AVR target configuration
# We would need ATMega256rfr2 with 32K RAM, but it's not supported by simavr.
# We instead use ATMega128rfr1 with 16K RAM, but modify its specification in
# simavr to bump the RAM to 32K.
# Once simavr supports ATMega256rfr2, or once mlkem-native has [an option for]
# lower stack usage, this should be changed.
AVR_MCU ?= atmega128rfr2
AVR_FREQ ?= 16000000UL

CFLAGS += \
	-Os \
	-fno-common \
	-ffunction-sections \
	-fdata-sections \
	-mmcu=$(AVR_MCU) \
	-DF_CPU=$(AVR_FREQ) \
	-DAVR_PLATFORM \
	-fno-fat-lto-objects

CFLAGS += $(CFLAGS_EXTRA)

# Non-standard stack end: 0x81FF = 0x200 + 8K instead of default 0x41FF
LDFLAGS += \
	-mmcu=$(AVR_MCU) \
	-Wl,--gc-sections \
	-Wl,--relax \
	-Wl,--defsym=__stack=0x81FF \
	-lprintf_min

# Add minimal AVR runtime
EXTRA_SOURCES = $(PLATFORM_PATH)/avr_wrapper.c
EXTRA_SOURCES_CFLAGS =

# Use simavr for execution
EXEC_WRAPPER := $(realpath $(PLATFORM_PATH)/exec_wrapper.py)
