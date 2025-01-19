# SPDX-License-Identifier: Apache-2.0

.PHONY: func kat nistkat acvp \
	func_512 kat_512 nistkat_512 acvp_512 \
	func_768 kat_768 nistkat_768 acvp_768 \
	func_1024 kat_1024 nistkat_1024 acvp_1024 \
	run_func run_kat run_nistkat run_acvp \
	run_func_512 run_kat_512 run_nistkat_512 run_acvp_512 \
	run_func_768 run_kat_768 run_nistkat_768 run_acvp_768 \
	run_func_1024 run_kat_1024 run_nistkat_1024 run_acvp_1024 \
	bench_512 bench_768 bench_1024 bench \
	run_bench_512 run_bench_768 run_bench_1024 run_bench \
	bench_components_512 bench_components_768 bench_components_1024 bench_components \
	run_bench_components_512 run_bench_components_768 run_bench_components_1024 run_bench_components \
	build test all \
	clean quickcheck check-defined-CYCLES

.DEFAULT_GOAL := build
all: build

W := $(EXEC_WRAPPER)

include test/mk/config.mk
include test/mk/components.mk
include test/mk/rules.mk

quickcheck: test

build: func nistkat kat acvp
	$(Q)echo "  Everything builds fine!"

test: run_kat run_nistkat run_func run_acvp
	$(Q)echo "  Everything checks fine!"

run_kat_512: kat_512
	$(W) $(MLKEM512_DIR)/bin/gen_KAT512 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  kat-sha256
run_kat_768: kat_768
	$(W) $(MLKEM768_DIR)/bin/gen_KAT768 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  kat-sha256
run_kat_1024: kat_1024
	$(W) $(MLKEM1024_DIR)/bin/gen_KAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024  kat-sha256
run_kat: run_kat_512 run_kat_768 run_kat_1024

run_nistkat_512: nistkat_512
	$(W) $(MLKEM512_DIR)/bin/gen_NISTKAT512 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  nistkat-sha256
run_nistkat_768: nistkat_768
	$(W) $(MLKEM768_DIR)/bin/gen_NISTKAT768 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  nistkat-sha256
run_nistkat_1024: nistkat_1024
	$(W) $(MLKEM1024_DIR)/bin/gen_NISTKAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024  nistkat-sha256
run_nistkat: run_nistkat_512 run_nistkat_768 run_nistkat_1024

run_func_512: func_512
	$(W) $(MLKEM512_DIR)/bin/test_mlkem512
run_func_768: func_768
	$(W) $(MLKEM768_DIR)/bin/test_mlkem768
run_func_1024: func_1024
	$(W) $(MLKEM1024_DIR)/bin/test_mlkem1024
run_func: run_func_512 run_func_768 run_func_1024

run_acvp: acvp
	python3 ./test/acvp_client.py

func_512:  $(MLKEM512_DIR)/bin/test_mlkem512
	$(Q)echo "  FUNC       ML-MEM-512:   $^"
func_768:  $(MLKEM768_DIR)/bin/test_mlkem768
	$(Q)echo "  FUNC       ML-MEM-768:   $^"
func_1024: $(MLKEM1024_DIR)/bin/test_mlkem1024
	$(Q)echo "  FUNC       ML-MEM-1024:  $^"
func: func_512 func_768 func_1024

nistkat_512: $(MLKEM512_DIR)/bin/gen_NISTKAT512
	$(Q)echo "  NISTKAT    ML-MEM-512:   $^"
nistkat_768: $(MLKEM768_DIR)/bin/gen_NISTKAT768
	$(Q)echo "  NISTKAT    ML-MEM-768:   $^"
nistkat_1024: $(MLKEM1024_DIR)/bin/gen_NISTKAT1024
	$(Q)echo "  NISTKAT    ML-MEM-1024:  $^"
nistkat: nistkat_512 nistkat_768 nistkat_1024

kat_512: $(MLKEM512_DIR)/bin/gen_KAT512
	$(Q)echo "  KAT        ML-MEM-512:   $^"
kat_768: $(MLKEM768_DIR)/bin/gen_KAT768
	$(Q)echo "  KAT        ML-MEM-768:   $^"
kat_1024: $(MLKEM1024_DIR)/bin/gen_KAT1024
	$(Q)echo "  KAT        ML-MEM-1024:  $^"
kat: kat_512 kat_768 kat_1024

acvp_512:  $(MLKEM512_DIR)/bin/acvp_mlkem512
	$(Q)echo "  ACVP       ML-MEM-512:   $^"
acvp_768:  $(MLKEM768_DIR)/bin/acvp_mlkem768
	$(Q)echo "  ACVP       ML-MEM-768:   $^"
acvp_1024: $(MLKEM1024_DIR)/bin/acvp_mlkem1024
	$(Q)echo "  ACVP       ML-MEM-1024:  $^"
acvp: acvp_512 acvp_768 acvp_1024

lib: $(BUILD_DIR)/libmlkem.a

# Enforce setting CYCLES make variable when
# building benchmarking binaries
check_defined = $(if $(value $1),, $(error $2))
check-defined-CYCLES:
	@:$(call check_defined,CYCLES,CYCLES undefined. Benchmarking requires setting one of NO PMU PERF M1)

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

# Use .WAIT to prevent parallel execution when -j is passed
run_bench: \
	run_bench_512 .WAIT\
	run_bench_768 .WAIT\
	run_bench_1024

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

# Use .WAIT to prevent parallel execution when -j is passed
run_bench_components: \
	run_bench_components_512 .WAIT\
	run_bench_components_768 .WAIT\
	run_bench_components_1024

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
	-make clean -C examples/bring_your_own_fips202 >/dev/null
	-make clean -C examples/custom_backend >/dev/null
	-make clean -C examples/mlkem_native_as_code_package >/dev/null
	-make clean -C examples/monolithic_build >/dev/null
	-make clean -C examples/monolithic_build_multilevel >/dev/null
	-make clean -C examples/multilevel_build >/dev/null
