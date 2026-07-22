# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

PLATFORM_PATH:=test/baremetal/platform/avr

CROSS_PREFIX=avr-
CC=gcc

# AVR target configuration
# ML-KEM-1024 (together with the RAM-resident test vectors) needs more than
# the 16K RAM of any MCU supported by simavr, so we use ATMega128rfr2 with its
# RAM specification in simavr bumped from 16K to the maximal 63.5K
# (0x0200-0xFFFF).
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
	-fno-fat-lto-objects \
	-DNTESTS_FUNC=10

# Trap on signed-shift UB; needs -fno-wrapv as avr-gcc defaults to -fwrapv.
# On UB, abort() in avr_wrapper.c is called.
CFLAGS += \
	-fno-wrapv \
	-fsanitize=undefined \
	-fsanitize-trap=undefined

CFLAGS += $(CFLAGS_EXTRA)

# Memory layout (data address space 0x0200-0xFFFF):
# - .data/.bss grow upwards from 0x0200 (data region length raised from the
#   default 16K to the full RAM size)
# - the argc/argv block sits at the top of RAM, with the stack growing
#   downwards from just below it (set up at runtime, see avr_wrapper.c)
LDFLAGS += \
	-mmcu=$(AVR_MCU) \
	-Wl,--gc-sections \
	-Wl,--relax \
	-Wl,--defsym=__DATA_REGION_LENGTH__=0xFC00 \
	-Wl,--undefined=_simavr_command_register \
	-Wl,--section-start=.mmcu=0x910000 \
	-lprintf_min

# Add minimal AVR runtime
EXTRA_SOURCES = $(PLATFORM_PATH)/avr_wrapper.c $(PLATFORM_PATH)/init7.S
EXTRA_SOURCES_CFLAGS = -I$(realpath $(dir $(shell which simavr))../include)

# Use simavr for execution
EXEC_WRAPPER := $(realpath $(PLATFORM_PATH)/exec_wrapper.py)
