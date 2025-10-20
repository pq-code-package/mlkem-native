# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

.PHONY: func kat acvp stack \
	func_512 kat_512 acvp_512 stack_512 \
	func_768 kat_768 acvp_768 stack_768 \
	func_1024 kat_1024 acvp_1024 stack_1024 \
	run_func run_kat run_acvp run_stack \
	run_func_512 run_kat_512 run_stack_512 \
	run_func_768 run_kat_768 run_stack_768 \
	run_func_1024 run_kat_1024 run_stack_1024 \
	bench_512 bench_768 bench_1024 bench \
	run_bench_512 run_bench_768 run_bench_1024 run_bench \
	bench_components_512 bench_components_768 bench_components_1024 bench_components \
	run_bench_components_512 run_bench_components_768 run_bench_components_1024 run_bench_components \
	build test all \
	clean quickcheck check-defined-CYCLES \
	size_512 size_768 size_1024 size \
	run_size_512 run_size_768 run_size_1024 run_size \
	host_info

SHELL := /bin/bash
.DEFAULT_GOAL := build

all: build

W := $(EXEC_WRAPPER)

include test/mk/config.mk
include test/mk/compiler.mk
include test/mk/auto.mk
include test/mk/components.mk
include test/mk/rules.mk

quickcheck: test

build: func kat acvp
	$(Q)echo "  Everything builds fine!"

test: run_kat run_func run_acvp run_unit
	$(Q)echo "  Everything checks fine!"

# Detect available SHA256 command
SHA256SUM := $(shell command -v shasum >/dev/null 2>&1 && echo "shasum -a 256" || (command -v sha256sum >/dev/null 2>&1 && echo "sha256sum" || echo ""))
ifeq ($(SHA256SUM),)
$(error Neither 'shasum' nor 'sha256sum' found. Please install one of these tools.)
endif

run_kat_512: kat_512
	set -o pipefail; $(W) $(MLKEM512_DIR)/bin/gen_KAT512 | $(SHA256SUM) | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512 kat-sha256
run_kat_768: kat_768
	set -o pipefail; $(W) $(MLKEM768_DIR)/bin/gen_KAT768 | $(SHA256SUM) | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  kat-sha256
run_kat_1024: kat_1024
	set -o pipefail; $(W) $(MLKEM1024_DIR)/bin/gen_KAT1024 | $(SHA256SUM) | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024  kat-sha256
run_kat: run_kat_512 run_kat_768 run_kat_1024

run_func_512: func_512
	$(W) $(MLKEM512_DIR)/bin/test_mlkem512
run_func_768: func_768
	$(W) $(MLKEM768_DIR)/bin/test_mlkem768
run_func_1024: func_1024
	$(W) $(MLKEM1024_DIR)/bin/test_mlkem1024
run_func: run_func_512 run_func_768 run_func_1024

run_unit_512: unit_512
	$(W) $(MLKEM512_DIR)/bin/test_unit512
run_unit_768: unit_768
	$(W) $(MLKEM768_DIR)/bin/test_unit768
run_unit_1024: unit_1024
	$(W) $(MLKEM1024_DIR)/bin/test_unit1024
run_unit: run_unit_512 run_unit_768 run_unit_1024

run_acvp: acvp
	python3 ./test/acvp_client.py $(if $(ACVP_VERSION),--version $(ACVP_VERSION))

func_512:  $(MLKEM512_DIR)/bin/test_mlkem512
	$(Q)echo "  FUNC       ML-KEM-512:   $^"
func_768:  $(MLKEM768_DIR)/bin/test_mlkem768
	$(Q)echo "  FUNC       ML-KEM-768:   $^"
func_1024: $(MLKEM1024_DIR)/bin/test_mlkem1024
	$(Q)echo "  FUNC       ML-KEM-1024:  $^"
func: func_512 func_768 func_1024

unit_512:  $(MLKEM512_DIR)/bin/test_unit512
	$(Q)echo "  UNIT       ML-KEM-512:   $^"
unit_768:  $(MLKEM768_DIR)/bin/test_unit768
	$(Q)echo "  UNIT       ML-KEM-768:   $^"
unit_1024: $(MLKEM1024_DIR)/bin/test_unit1024
	$(Q)echo "  UNIT       ML-KEM-1024:  $^"
unit: unit_512 unit_768 unit_1024

kat_512: $(MLKEM512_DIR)/bin/gen_KAT512
	$(Q)echo "  KAT        ML-KEM-512:   $^"
kat_768: $(MLKEM768_DIR)/bin/gen_KAT768
	$(Q)echo "  KAT        ML-KEM-768:   $^"
kat_1024: $(MLKEM1024_DIR)/bin/gen_KAT1024
	$(Q)echo "  KAT        ML-KEM-1024:  $^"
kat: kat_512 kat_768 kat_1024

acvp_512:  $(MLKEM512_DIR)/bin/acvp_mlkem512
	$(Q)echo "  ACVP       ML-KEM-512:   $^"
acvp_768:  $(MLKEM768_DIR)/bin/acvp_mlkem768
	$(Q)echo "  ACVP       ML-KEM-768:   $^"
acvp_1024: $(MLKEM1024_DIR)/bin/acvp_mlkem1024
	$(Q)echo "  ACVP       ML-KEM-1024:  $^"
acvp: acvp_512 acvp_768 acvp_1024

ifeq ($(HOST_PLATFORM),Linux-aarch64)
# valgrind does not work with the AArch64 SHA3 extension
# Use armv8-a as the target architecture, overwriting a
# potential earlier addition of armv8.4-a+sha3.
$(MLKEM512_DIR)/bin/test_stack512:   CFLAGS += -march=armv8-a
$(MLKEM768_DIR)/bin/test_stack768:   CFLAGS += -march=armv8-a
$(MLKEM1024_DIR)/bin/test_stack1024: CFLAGS += -march=armv8-a
endif

stack_512: $(MLKEM512_DIR)/bin/test_stack512
	$(Q)echo "  STACK      ML-KEM-512:   $^"
stack_768: $(MLKEM768_DIR)/bin/test_stack768
	$(Q)echo "  STACK      ML-KEM-768:   $^"
stack_1024: $(MLKEM1024_DIR)/bin/test_stack1024
	$(Q)echo "  STACK      ML-KEM-1024:  $^"
stack: stack_512 stack_768 stack_1024

run_stack_512: stack_512
	$(Q)python3 scripts/stack $(MLKEM512_DIR)/bin/test_stack512 --build-dir $(MLKEM512_DIR) $(STACK_ANALYSIS_FLAGS)
run_stack_768: stack_768
	$(Q)python3 scripts/stack $(MLKEM768_DIR)/bin/test_stack768 --build-dir $(MLKEM768_DIR) $(STACK_ANALYSIS_FLAGS)
run_stack_1024: stack_1024
	$(Q)python3 scripts/stack $(MLKEM1024_DIR)/bin/test_stack1024 --build-dir $(MLKEM1024_DIR) $(STACK_ANALYSIS_FLAGS)
run_stack: run_stack_512 run_stack_768 run_stack_1024

lib: $(BUILD_DIR)/libmlkem.a $(BUILD_DIR)/libmlkem512.a $(BUILD_DIR)/libmlkem768.a $(BUILD_DIR)/libmlkem1024.a

# Enforce setting CYCLES make variable when
# building benchmarking binaries
check_defined = $(if $(value $1),, $(error $2))
check-defined-CYCLES:
	@:$(call check_defined,CYCLES,CYCLES undefined. Benchmarking requires setting one of NO PMU PERF MAC)

bench_512: check-defined-CYCLES \
	$(MLKEM512_DIR)/bin/bench_mlkem512
bench_768: check-defined-CYCLES \
	$(MLKEM768_DIR)/bin/bench_mlkem768
bench_1024: check-defined-CYCLES \
	$(MLKEM1024_DIR)/bin/bench_mlkem1024
bench: bench_512 bench_768 bench_1024

run_bench_512: bench_512
	$(W) $(MLKEM512_DIR)/bin/bench_mlkem512
run_bench_768: bench_768
	$(W) $(MLKEM768_DIR)/bin/bench_mlkem768
run_bench_1024: bench_1024
	$(W) $(MLKEM1024_DIR)/bin/bench_mlkem1024
run_bench: bench
	$(W) $(MLKEM512_DIR)/bin/bench_mlkem512
	$(W) $(MLKEM768_DIR)/bin/bench_mlkem768
	$(W) $(MLKEM1024_DIR)/bin/bench_mlkem1024

bench_components_512: check-defined-CYCLES \
	$(MLKEM512_DIR)/bin/bench_components_mlkem512
bench_components_768: check-defined-CYCLES \
	$(MLKEM768_DIR)/bin/bench_components_mlkem768
bench_components_1024: check-defined-CYCLES \
	$(MLKEM1024_DIR)/bin/bench_components_mlkem1024
bench_components: bench_components_512 bench_components_768 bench_components_1024

run_bench_components_512: bench_components_512
	$(W) $(MLKEM512_DIR)/bin/bench_components_mlkem512
run_bench_components_768: bench_components_768
	$(W) $(MLKEM768_DIR)/bin/bench_components_mlkem768
run_bench_components_1024: bench_components_1024
	$(W) $(MLKEM1024_DIR)/bin/bench_components_mlkem1024
run_bench_components: bench_components
	$(W) $(MLKEM512_DIR)/bin/bench_components_mlkem512
	$(W) $(MLKEM768_DIR)/bin/bench_components_mlkem768
	$(W) $(MLKEM1024_DIR)/bin/bench_components_mlkem1024

size_512: $(BUILD_DIR)/libmlkem512.a
size_768: $(BUILD_DIR)/libmlkem768.a
size_1024: $(BUILD_DIR)/libmlkem1024.a
size: size_512 size_768 size_1024

run_size_512: size_512
	$(Q)echo "size $(BUILD_DIR)/libmlkem512.a"
	$(Q)$(SIZE) $(BUILD_DIR)/libmlkem512.a | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)

run_size_768: size_768
	$(Q)echo "size $(BUILD_DIR)/libmlkem768.a"
	$(Q)$(SIZE) $(BUILD_DIR)/libmlkem768.a | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)

run_size_1024: size_1024
	$(Q)echo "size $(BUILD_DIR)/libmlkem1024.a"
	$(Q)$(SIZE) $(BUILD_DIR)/libmlkem1024.a | (read header; echo "$$header"; awk '$$5 != 0' | sort -k5 -n -r)


run_size: \
	run_size_512 \
	run_size_768 \
	run_size_1024

# Display host and compiler feature detection information
# Shows which architectural features are supported by both the compiler and host CPU
# Usage: make host_info [AUTO=0|1] [CROSS_PREFIX=...]
host_info:
	@echo "=== Host and Compiler Feature Detection ==="
	@echo "Host Platform: $(HOST_PLATFORM)"
	@echo "Target Architecture: $(ARCH)"
	@echo "Compiler: $(CC)"
	@echo "Cross Prefix: $(if $(CROSS_PREFIX),$(CROSS_PREFIX),<none>)"
	@echo "AUTO: $(AUTO)"
	@echo ""
ifeq ($(ARCH),x86_64)
	@echo "=== x86_64 Feature Support ==="
	@echo "AVX2: Host $(if $(filter 1,$(MK_HOST_SUPPORTS_AVX2)),✅,❌) Compiler $(if $(filter 1,$(MK_COMPILER_SUPPORTS_AVX2)),✅,❌)"
	@echo "SSE2: Host $(if $(filter 1,$(MK_HOST_SUPPORTS_SSE2)),✅,❌) Compiler $(if $(filter 1,$(MK_COMPILER_SUPPORTS_SSE2)),✅,❌)"
	@echo "BMI2: Host $(if $(filter 1,$(MK_HOST_SUPPORTS_BMI2)),✅,❌) Compiler $(if $(filter 1,$(MK_COMPILER_SUPPORTS_BMI2)),✅,❌)"
else ifeq ($(ARCH),aarch64)
	@echo "=== AArch64 Feature Support ==="
	@echo "SHA3: Host $(if $(filter 1,$(MK_HOST_SUPPORTS_SHA3)),✅,❌) Compiler $(if $(filter 1,$(MK_COMPILER_SUPPORTS_SHA3)),✅,❌)"
else
	@echo "=== Architecture Not Supported ==="
	@echo "No specific feature detection available for $(ARCH)"
endif

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
	-make clean -C examples/bring_your_own_fips202 >/dev/null
	-make clean -C examples/bring_your_own_fips202_static >/dev/null
	-make clean -C examples/custom_backend >/dev/null
	-make clean -C examples/basic >/dev/null
	-make clean -C examples/basic_deterministic >/dev/null
	-make clean -C examples/monolithic_build >/dev/null
	-make clean -C examples/monolithic_build_native >/dev/null
	-make clean -C examples/monolithic_build_multilevel >/dev/null
	-make clean -C examples/monolithic_build_multilevel_native >/dev/null
	-make clean -C examples/multilevel_build >/dev/null
	-make clean -C examples/multilevel_build_native >/dev/null
