# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

PLATFORM_PATH := test/zephyr

# BUILD_DIR is set by the top-level Makefile after this file is included;
# define it here too so the explicit bin rules below expand to the right path.
BUILD_DIR ?= test/build

# ZEPHYR_TARGET=<key> selects a target. Each key maps to a Zephyr board and the
# QEMU machine emulating it; add a board with a row below.
ZEPHYR_TARGET ?= mps3-an547

ZEPHYR_BOARD_mps2-an385 := mps2/an385
ZEPHYR_QEMU_mps2-an385  := mps2-an385                                # Cortex-M3
ZEPHYR_BOARD_mps2-an386 := mps2/an386
ZEPHYR_QEMU_mps2-an386  := mps2-an386                                # Cortex-M4
ZEPHYR_BOARD_mps2-an500 := mps2/an500
ZEPHYR_QEMU_mps2-an500  := mps2-an500                                # Cortex-M7
ZEPHYR_BOARD_mps2-an521 := mps2/an521/cpu0
ZEPHYR_QEMU_mps2-an521  := mps2-an521                                # Cortex-M33
ZEPHYR_BOARD_mps3-an547 := mps3/corstone300/an547
ZEPHYR_QEMU_mps3-an547  := mps3-an547                                # Cortex-M55

ZEPHYR_FIPS202_BACKEND_mps3-an547 := fips202/native/armv81m/mve.h

ZEPHYR_TARGETS := mps2-an385 mps2-an386 mps2-an500 mps2-an521 mps3-an547

ZEPHYR_BOARD := $(ZEPHYR_BOARD_$(ZEPHYR_TARGET))
export QEMU_MACHINE := $(strip $(ZEPHYR_QEMU_$(ZEPHYR_TARGET)))

ifeq ($(ZEPHYR_BOARD),)
$(error Unknown ZEPHYR_TARGET '$(ZEPHYR_TARGET)'. Supported: $(ZEPHYR_TARGETS))
endif

# The test binaries are built by Zephyr's CMake (which uses its own arm
# toolchain via the .#zephyr dev shell), not the generic Make rules. The
# top-level targets still attach the usual object/library prerequisites to the
# bin paths; with OPT=0 those are portable host objects that compile cleanly
# and are simply discarded (the Zephyr ELF is copied over them).
OPT ?= 0

# Native backends are an OPT=1 feature (an547 builds the Armv8.1-M MVE backend).
ZEPHYR_FIPS202_BACKEND := $(if $(filter 1,$(OPT)),$(strip $(ZEPHYR_FIPS202_BACKEND_$(ZEPHYR_TARGET))))

ZEPHYR_APP := $(PLATFORM_PATH)/app
ZEPHYR_BUILD_DIR := $(BUILD_DIR)/zephyr/$(ZEPHYR_TARGET)

# Build a test as a Zephyr application and drop the resulting ELF at the path
# the top-level Makefile expects. An explicit rule for the exact bin path wins
# over the generic link pattern rule in test/mk/rules.mk.
#   $(1) level  $(2) bin name  $(3) test source (repo-relative)  $(4) extra -D
define ZEPHYR_BIN
$(BUILD_DIR)/mlkem$(1)/bin/$(2):
	$$(Q)echo "  ZEPHYR  $(ZEPHYR_TARGET) ML-KEM-$(1): $(3)"
	$$(Q)cmake -GNinja -S $(ZEPHYR_APP) -B $(ZEPHYR_BUILD_DIR)/$(2) \
		-DBOARD=$(ZEPHYR_BOARD) \
		-DZEPHYR_NATIVE_ROOT=$(CURDIR) \
		-DZEPHYR_LEVEL=$(1) \
		-DZEPHYR_TEST_SRC=$(3) \
		-DZEPHYR_TEST_DEFS="NTESTS_FUNC=3 NTESTS_KAT=100 MLK_BENCHMARK_NTESTS=10 MLK_BENCHMARK_NITERATIONS=10 MLK_BENCHMARK_NWARMUP=10" \
		-DZEPHYR_FIPS202_BACKEND=$(ZEPHYR_FIPS202_BACKEND) \
		$(if $(ZEPHYR_FIPS202_BACKEND),-DCONFIG_FIPS202_MVE_BACKEND=y) \
		$(4) \
		-DUSER_CACHE_DIR=$(abspath $(ZEPHYR_BUILD_DIR)/$(2)/.cache) \
		>/dev/null
	$$(Q)cmake --build $(ZEPHYR_BUILD_DIR)/$(2) >/dev/null
	$$(Q)[ -d $$(@D) ] || mkdir -p $$(@D)
	$$(Q)cp $(ZEPHYR_BUILD_DIR)/$(2)/zephyr/zephyr.elf $$@
endef

$(eval $(call ZEPHYR_BIN,512,test_mlkem512,test/src/test_mlkem.c))
$(eval $(call ZEPHYR_BIN,768,test_mlkem768,test/src/test_mlkem.c))
$(eval $(call ZEPHYR_BIN,1024,test_mlkem1024,test/src/test_mlkem.c))

$(eval $(call ZEPHYR_BIN,512,gen_KAT512,test/src/gen_KAT.c))
$(eval $(call ZEPHYR_BIN,768,gen_KAT768,test/src/gen_KAT.c))
$(eval $(call ZEPHYR_BIN,1024,gen_KAT1024,test/src/gen_KAT.c))

$(eval $(call ZEPHYR_BIN,512,acvp_mlkem512,test/acvp/acvp_mlkem.c))
$(eval $(call ZEPHYR_BIN,768,acvp_mlkem768,test/acvp/acvp_mlkem.c))
$(eval $(call ZEPHYR_BIN,1024,acvp_mlkem1024,test/acvp/acvp_mlkem.c))

$(eval $(call ZEPHYR_BIN,512,wycheproof_mlkem512,test/wycheproof/wycheproof_mlkem.c))
$(eval $(call ZEPHYR_BIN,768,wycheproof_mlkem768,test/wycheproof/wycheproof_mlkem.c))
$(eval $(call ZEPHYR_BIN,1024,wycheproof_mlkem1024,test/wycheproof/wycheproof_mlkem.c))

$(eval $(call ZEPHYR_BIN,512,bench_mlkem512,test/bench/bench_mlkem.c,-DZEPHYR_TEST_HAL=ON))
$(eval $(call ZEPHYR_BIN,768,bench_mlkem768,test/bench/bench_mlkem.c,-DZEPHYR_TEST_HAL=ON))
$(eval $(call ZEPHYR_BIN,1024,bench_mlkem1024,test/bench/bench_mlkem.c,-DZEPHYR_TEST_HAL=ON))

$(eval $(call ZEPHYR_BIN,512,bench_components_mlkem512,test/bench/bench_components_mlkem.c,-DZEPHYR_TEST_HAL=ON))
$(eval $(call ZEPHYR_BIN,768,bench_components_mlkem768,test/bench/bench_components_mlkem.c,-DZEPHYR_TEST_HAL=ON))
$(eval $(call ZEPHYR_BIN,1024,bench_components_mlkem1024,test/bench/bench_components_mlkem.c,-DZEPHYR_TEST_HAL=ON))

EXEC_WRAPPER := $(abspath $(PLATFORM_PATH)/exec_wrapper.py)
