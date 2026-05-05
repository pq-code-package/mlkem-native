# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

PLATFORM_PATH:=test/baremetal/platform/nucleo-n657x0-q
BUILD_DIR ?= test/build

CROSS_PREFIX=arm-none-eabi-
CC=gcc

# Use PMU cycle counting by default
CYCLES ?= PMU

# Short benchmark runs for testing
MLK_BENCHMARK_NWARMUP ?= 1
MLK_BENCHMARK_NITERATIONS ?= 1
MLK_BENCHMARK_NTESTS ?= 1

CFLAGS += \
	-DMLK_BENCHMARK_NWARMUP=$(MLK_BENCHMARK_NWARMUP) \
	-DMLK_BENCHMARK_NITERATIONS=$(MLK_BENCHMARK_NITERATIONS) \
	-DMLK_BENCHMARK_NTESTS=$(MLK_BENCHMARK_NTESTS)

CFLAGS += \
	-O3 -g \
	-Wall -Wextra -Wshadow \
	-Wno-pedantic \
	-Wno-redundant-decls \
	-Wno-missing-prototypes \
	-fno-common \
	-ffunction-sections \
	-fdata-sections \
	--sysroot=$(SYSROOT) \
	-DDEVICE=nucleo-n657x0-q \
	-DSTM32N657xx \
	-DNTESTS_FUNC=1 \
	-I$(NUCLEO_N657X0_Q_PATH) \
	-I$(NUCLEO_N657X0_Q_PATH)/Inc \
	-I$(NUCLEO_N657X0_Q_PATH)/Drivers/STM32N6xx_HAL_Driver/Inc \
	-I$(NUCLEO_N657X0_Q_PATH)/Drivers/CMSIS/Core/Include \
	-I$(NUCLEO_N657X0_Q_PATH)/Drivers/CMSIS/Core/Include/m-profile \
	-I$(NUCLEO_N657X0_Q_PATH)/Drivers/CMSIS/Device/ST \
	-I$(NUCLEO_N657X0_Q_PATH)/Drivers/CMSIS/Device/ST/STM32N6xx/Include/ \
	-DSEMIHOSTING \


ARCH_FLAGS += \
	-mcmse \
	-march=armv8.1-m.main+mve.fp \
	-mcpu=cortex-m55 \
	-mthumb \
	-mfloat-abi=hard -mfpu=fpv5-sp-d16

# TODO(GAP): If the Cube template (or GCC/newlib build) expects softfp, use:
#   -mfloat-abi=softfp  (and keep -mfpu)

SEMIHOST_SPECS := --specs=rdimon.specs

CFLAGS += \
    $(ARCH_FLAGS)

CFLAGS += $(CFLAGS_EXTRA)

# Try to auto-detect a GCC linker script from the FSBL or CMSIS template; fall back to linker.ld if present
# Prefer linker scripts under gcc/linker/, fall back to other locations.
# Try to pick an N657-specific script first.
# Use custom RAM-only secure linker script for this platform
LDSCRIPT := $(PLATFORM_PATH)/linker/ram_secure.ld

# Auto-detect startup assembly case and optional board glue
# Auto-detect startup assembly for STM32N6 family (prefer n657 if present)
STARTUP := $(firstword \
    $(wildcard $(NUCLEO_N657X0_Q_PATH)/gcc/startup_stm32n657xx.[sS]) \
    $(wildcard $(NUCLEO_N657X0_Q_PATH)/gcc/startup_stm32n6*.[sS]) \
    $(wildcard $(NUCLEO_N657X0_Q_PATH)/gcc/startup_stm32n*.[sS]) \
)
# MSP     := $(firstword $(wildcard $(NUCLEO_N657X0_Q_PATH)/stm32n6xx_hal_msp.c))
IT      := $(firstword $(wildcard $(NUCLEO_N657X0_Q_PATH)/stm32n6xx_it.c))
HAL_SRCS :=
HAL_CORE := $(firstword $(wildcard $(NUCLEO_N657X0_Q_PATH)/Drivers/STM32N6xx_HAL_Driver/Src/stm32n6xx_hal.c))

LDFLAGS += \
	-Wl,--gc-sections \
	-Wl,--no-warn-rwx-segments \
	-L.

LDFLAGS += \
	$(SEMIHOST_SPECS) \
	-Wl,--wrap=main \
	-ffreestanding \
	-T$(LDSCRIPT) \
	$(ARCH_FLAGS)

LDLIBS += -lc -lrdimon

# Extra sources to be included in test binaries
EXTRA_SOURCES = \
    $(PLATFORM_PATH)/src/cmdline.c \
    $(PLATFORM_PATH)/src/cmdline_region.c \
    $(PLATFORM_PATH)/src/flexmem_layout_check.c \
    $(PLATFORM_PATH)/src/semihosting_syscall.c \
    $(NUCLEO_N657X0_Q_PATH)/clock_config.c \
    $(NUCLEO_N657X0_Q_PATH)/system_stm32n6xx.c \
    $(STARTUP) \
    $(IT) \
    $(HAL_CORE) \
    $(NUCLEO_N657X0_Q_PATH)/integration_argv.c \
	$(NUCLEO_N657X0_Q_PATH)/Drivers/STM32N6xx_HAL_Driver/Src/stm32n6xx_hal_rcc.c \
	$(NUCLEO_N657X0_Q_PATH)/Drivers/STM32N6xx_HAL_Driver/Src/stm32n6xx_hal_cortex.c \
	$(NUCLEO_N657X0_Q_PATH)/Drivers/STM32N6xx_HAL_Driver/Src/stm32n6xx_hal_rcc_ex.c \
	$(NUCLEO_N657X0_Q_PATH)/Drivers/STM32N6xx_HAL_Driver/Src/stm32n6xx_hal_pwr.c \
	$(NUCLEO_N657X0_Q_PATH)/Drivers/STM32N6xx_HAL_Driver/Src/stm32n6xx_hal_pwr_ex.c

    # $(MSP) \

# The Cube/CMSIS and HAL files often fail compilation with strict warnings; relax for these files
EXTRA_SOURCES_CFLAGS = -Wno-error -Wno-conversion -Wno-sign-conversion -Wno-unused-parameter -Wno-missing-prototypes -Wno-maybe-uninitialized -Wno-unused-function

# Avoid duplicate __wrap_main by excluding the generic integration_argv.c (not generated anymore)
EXTRA_SOURCES := $(filter-out %/integration_argv.c,$(EXTRA_SOURCES))

EXEC_WRAPPER := $(realpath $(PLATFORM_PATH)/exec_wrapper.py)

FLEXMEM_CONFIG_ELF ?= $(BUILD_DIR)/nucleo-n657x0-q/flexmem_config.elf
FLEXMEM_CONFIG_LDSCRIPT := $(PLATFORM_PATH)/linker/flexmem_config_default.ld
FLEXMEM_CONFIG_SOURCES := \
    $(PLATFORM_PATH)/src/flexmem_config.c \
    $(NUCLEO_N657X0_Q_PATH)/system_stm32n6xx.c \
    $(STARTUP)

.PHONY: flexmem_config run_flexmem_config run_flexmem_test

run_kat run_acvp run_bench run_func run_unit run_alloc: run_flexmem_config

flexmem_config: $(FLEXMEM_CONFIG_ELF)

$(FLEXMEM_CONFIG_ELF): $(FLEXMEM_CONFIG_SOURCES) $(FLEXMEM_CONFIG_LDSCRIPT)
	$(Q)echo "  LD      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) $(CFLAGS) $(EXTRA_SOURCES_CFLAGS) \
		-ffreestanding \
		-Wl,--gc-sections -Wl,--no-warn-rwx-segments \
		$(SEMIHOST_SPECS) \
		-T$(FLEXMEM_CONFIG_LDSCRIPT) $(ARCH_FLAGS) \
		-o $@ $(FLEXMEM_CONFIG_SOURCES) -lc -lrdimon

run_flexmem_config: flexmem_config
	$(Q)python3 $(PLATFORM_PATH)/flexmem_configure.py $(FLEXMEM_CONFIG_ELF)

run_flexmem_test: flexmem_config func_512
	$(Q)python3 $(PLATFORM_PATH)/flexmem_configure.py $(FLEXMEM_CONFIG_ELF)
	$(Q)python3 $(PLATFORM_PATH)/run_test_after_flexmem.py $(MLKEM512_DIR)/bin/test_mlkem512
