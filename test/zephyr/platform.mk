# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# Zephyr test platform for QEMU-emulated Arm MPS boards.
#
# Each test binary is built as a Zephyr application by CMake (which owns the arm
# toolchain, per-board arch flags and libc via the .#zephyr dev shell). The
# generic rules don't link these; CUSTOM_BUILD (below, see test/mk/rules.mk)
# drives the CMake build from the binary's TEST_SRCS, set by components.mk --
# adding a test binary there needs no change here.

PLATFORM_PATH := test/zephyr

# BUILD_DIR is set by the top-level Makefile after this file is included;
# define it here too so CUSTOM_BUILD below expands to the right path.
BUILD_DIR ?= test/build

# ZEPHYR_TARGET=<key> selects a target. QEMU targets map to both a Zephyr board
# and the QEMU machine emulating it; hardware targets map to a Zephyr board and
# provide their own execution wrapper. Add a target with a row below.
ZEPHYR_TARGET ?= mps3-an547

ZEPHYR_BOARD_mps2-an385 := mps2/an385
ZEPHYR_QEMU_mps2-an385  := mps2-an385                    # Cortex-M3
ZEPHYR_BOARD_mps2-an386 := mps2/an386
ZEPHYR_QEMU_mps2-an386  := mps2-an386                    # Cortex-M4
ZEPHYR_BOARD_mps2-an500 := mps2/an500
ZEPHYR_QEMU_mps2-an500  := mps2-an500                    # Cortex-M7
ZEPHYR_BOARD_mps2-an521 := mps2/an521/cpu0
ZEPHYR_QEMU_mps2-an521  := mps2-an521                    # Cortex-M33
ZEPHYR_BOARD_mps3-an547 := mps3/corstone300/an547
ZEPHYR_QEMU_mps3-an547  := mps3-an547                    # Cortex-M55
ZEPHYR_BOARD_nucleo-n657x0-q := nucleo_n657x0_q          # Cortex-M55 (hardware)

ZEPHYR_FIPS202_BACKEND_mps3-an547 := fips202/native/armv81m/mve.h
ZEPHYR_FIPS202_BACKEND_nucleo-n657x0-q := fips202/native/armv81m/mve.h

ZEPHYR_TARGETS := mps2-an385 mps2-an386 mps2-an500 mps2-an521 mps3-an547 nucleo-n657x0-q

ZEPHYR_BOARD := $(ZEPHYR_BOARD_$(ZEPHYR_TARGET))
export QEMU_MACHINE := $(strip $(ZEPHYR_QEMU_$(ZEPHYR_TARGET)))
ZEPHYR_IS_NUCLEO_N657X0_Q := $(filter nucleo-n657x0-q,$(ZEPHYR_TARGET))

ifneq ($(ZEPHYR_IS_NUCLEO_N657X0_Q),)
CROSS_PREFIX ?= arm-none-eabi-
CC = gcc
endif

ifeq ($(ZEPHYR_BOARD),)
$(error Unknown ZEPHYR_TARGET '$(ZEPHYR_TARGET)'. Supported: $(ZEPHYR_TARGETS))
endif

# CUSTOM_BUILD must be set before components.mk is included so it switches that
# file to source prerequisites (it is: the top-level Makefile includes us first).
OPT ?= 0

# Native backends are an OPT=1 feature (an547 builds the Armv8.1-M MVE backend).
ZEPHYR_FIPS202_BACKEND := $(if $(filter 1,$(OPT)),$(strip $(ZEPHYR_FIPS202_BACKEND_$(ZEPHYR_TARGET))))

ZEPHYR_APP := $(PLATFORM_PATH)/app
ZEPHYR_BUILD_DIR := $(BUILD_DIR)/zephyr/$(ZEPHYR_TARGET)
ZEPHYR_ACTIVE_TARGET := $(BUILD_DIR)/zephyr/.active-target
ZEPHYR_APP_INPUTS := \
	$(ZEPHYR_APP)/CMakeLists.txt \
	$(ZEPHYR_APP)/Kconfig \
	$(ZEPHYR_APP)/prj.conf \
	$(ZEPHYR_APP)/nucleo_n657x0_q.conf \
	$(ZEPHYR_APP)/shim.c \
	$(ZEPHYR_APP)/shim_nucleo_n657x0_q.c \
	$(ZEPHYR_APP)/nucleo_n657x0_q.overlay
ZEPHYR_NUCLEO_PLATFORM_PATH := $(PLATFORM_PATH)/nucleo_n657x0_q
ZEPHYR_NUCLEO_OVERLAY := $(abspath $(ZEPHYR_APP)/nucleo_n657x0_q.overlay)
ZEPHYR_NUCLEO_CONF := $(abspath $(ZEPHYR_APP)/nucleo_n657x0_q.conf)
ZEPHYR_TARGET_CMAKE_ARGS := $(if $(ZEPHYR_IS_NUCLEO_N657X0_Q),\
	-DZEPHYR_NUCLEO_N657X0_Q=ON \
	-DEXTRA_CONF_FILE=$(ZEPHYR_NUCLEO_CONF) \
	-DDTC_OVERLAY_FILE=$(ZEPHYR_NUCLEO_OVERLAY))

# Test binary output paths are shared across ZEPHYR_TARGET values, while the
# CMake build directory is target-specific. Keep a lightweight marker containing
# the last requested target, and only touch it when the target changes. Binaries
# depending on this marker are then rebuilt after a target switch without
# forcing a clean rebuild when the target is unchanged.
.PHONY: zephyr_target_marker_force
$(ZEPHYR_ACTIVE_TARGET): zephyr_target_marker_force
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)if [ ! -f $@ ] || [ "$$(cat $@)" != "$(ZEPHYR_TARGET)" ]; then \
		echo "$(ZEPHYR_TARGET)" > $@; \
	fi

# Per-binary CMake build dir, keyed on $(notdir $@) so binaries build in
# parallel. Recipe-expanded, so $@ is the specific bin being built.
ZEPHYR_OUT = $(ZEPHYR_BUILD_DIR)/$(notdir $@)

# Shrink the test iteration counts (the sources default them higher, sized for
# native hardware): QEMU is far slower. On CFLAGS so they forward below.
CFLAGS += -DNTESTS_FUNC=3 -DNTESTS_KAT=100 \
	-DMLK_BENCHMARK_NTESTS=10 -DMLK_BENCHMARK_NITERATIONS=10 -DMLK_BENCHMARK_NWARMUP=10 \
	-DNUM_RANDOM_TESTS=100 -DNUM_RANDOM_TESTS_REJ_UNIFORM=100 -DMAX_INTT_CONSTANT_COEFF=512

# The binary's CFLAGS, forwarded to the CMake build (which applies them to the
# mlkem amalgamation and test sources alike). '=' not ':=', so the recipe-time
# $(CFLAGS) includes the binary's target-specific additions (e.g.
# -DMLK_STATIC_TESTABLE= for test_unit, -DMLK_CONFIG_FILE="..." for test_alloc).
# Two rewrites:
#   - -Imlkem -> absolute, as CMake builds from its own dir, not the repo root
#     (and the alloc config path is relative to -Imlkem);
#   - \" -> \\", so one level of quoting survives each of the recipe shell and
#     CMake's separate_arguments and reaches the compiler intact.
# Requires AUTO=0 (see .github/workflows/zephyr.yml): the host-arch flags AUTO=1
# adds must not reach the Zephyr toolchain, which selects the target arch itself.
ZEPHYR_TEST_CFLAGS = $(subst \",\\\",$(patsubst -Imlkem,-I$(abspath mlkem),$(CFLAGS)))

CUSTOM_BUILD = \
	echo "  ZEPHYR  $(ZEPHYR_TARGET): $(notdir $@)" && \
	cmake -GNinja -S $(ZEPHYR_APP) -B $(ZEPHYR_OUT) \
		-DBOARD=$(ZEPHYR_BOARD) \
		-DZEPHYR_NATIVE_ROOT=$(CURDIR) \
		-DZEPHYR_TEST_SRCS="$(strip $(TEST_SRCS))" \
		-DZEPHYR_TEST_CFLAGS="$(ZEPHYR_TEST_CFLAGS)" \
		-DZEPHYR_FIPS202_BACKEND=$(ZEPHYR_FIPS202_BACKEND) \
		$(if $(ZEPHYR_FIPS202_BACKEND),-DCONFIG_FIPS202_MVE_BACKEND=y) \
		$(ZEPHYR_TARGET_CMAKE_ARGS) \
		-DUSER_CACHE_DIR=$(abspath $(ZEPHYR_OUT)/.cache) \
		>/dev/null && \
	cmake --build $(ZEPHYR_OUT) >/dev/null && \
	cp $(ZEPHYR_OUT)/zephyr/zephyr.elf $@

# A custom build links the test sources directly rather than from objects, so
# nothing otherwise makes the bins depend on the Zephyr app inputs or the
# active-target marker. components.mk attaches CUSTOM_BUILD_DEPS to every test
# binary (in its CUSTOM_BUILD branch), so a CMakeLists/shim/overlay edit or a
# target switch forces a rebuild. Set here (before components.mk is included).
CUSTOM_BUILD_DEPS := $(ZEPHYR_ACTIVE_TARGET) $(ZEPHYR_APP_INPUTS)

ifeq ($(ZEPHYR_IS_NUCLEO_N657X0_Q),)
EXEC_WRAPPER := $(abspath $(PLATFORM_PATH)/exec_wrapper.py)
else
EXEC_WRAPPER := $(abspath $(ZEPHYR_NUCLEO_PLATFORM_PATH)/exec_wrapper.py)
endif
