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
	bench_components_512 bench_components_768 bench_components_1024 bench_components \
	buildall checkall all \
	clean quickcheck check-defined-CYCLES

.DEFAULT_GOAL := buildall
all: quickcheck

include mk/config.mk
include mk/crypto.mk
include mk/schemes.mk
include mk/rules.mk

quickcheck: checkall

buildall: func nistkat kat acvp
	$(Q)echo "  Everything builds fine!"

checkall: run_kat run_nistkat run_func run_acvp
	$(Q)echo "  Everything checks fine!"

run_kat_512: kat_512
	$(MLKEM512_DIR)/bin/gen_KAT512 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  kat-sha256
run_kat_768: kat_768
	$(MLKEM768_DIR)/bin/gen_KAT768 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  kat-sha256
run_kat_1024: kat_1024
	$(MLKEM1024_DIR)/bin/gen_KAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024  kat-sha256
run_kat: run_kat_512 run_kat_768 run_kat_1024

run_nistkat_512: nistkat_512
	$(MLKEM512_DIR)/bin/gen_NISTKAT512 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  nistkat-sha256
run_nistkat_768: nistkat_768
	$(MLKEM768_DIR)/bin/gen_NISTKAT768 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  nistkat-sha256
run_nistkat_1024: nistkat_1024
	$(MLKEM1024_DIR)/bin/gen_NISTKAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024  nistkat-sha256
run_nistkat: run_nistkat_512 run_nistkat_768 run_nistkat_1024

run_func_512: func_512
	$(MLKEM512_DIR)/bin/test_mlkem512
run_func_768: func_768
	$(MLKEM768_DIR)/bin/test_mlkem768
run_func_1024: func_1024
	$(MLKEM1024_DIR)/bin/test_mlkem1024
run_func: run_func_512 run_func_768 run_func_1024

run_acvp: acvp
	python3 ./test/acvp_client.py

func_512:  $(MLKEM512_DIR)/bin/test_mlkem512
func_768:  $(MLKEM768_DIR)/bin/test_mlkem768
func_1024: $(MLKEM1024_DIR)/bin/test_mlkem1024
func: func_512 func_768 func_1024

nistkat_512: $(MLKEM512_DIR)/bin/gen_NISTKAT512
nistkat_768: $(MLKEM768_DIR)/bin/gen_NISTKAT768
nistkat_1024: $(MLKEM1024_DIR)/bin/gen_NISTKAT1024
nistkat: nistkat_512 nistkat_768 nistkat_1024

kat_512: $(MLKEM512_DIR)/bin/gen_KAT512
kat_768: $(MLKEM768_DIR)/bin/gen_KAT768
kat_1024: $(MLKEM1024_DIR)/bin/gen_KAT1024
kat: kat_512 kat_768 kat_1024

acvp_512:  $(MLKEM512_DIR)/bin/acvp_mlkem512
acvp_768:  $(MLKEM768_DIR)/bin/acvp_mlkem768
acvp_1024: $(MLKEM1024_DIR)/bin/acvp_mlkem1024
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

bench_components_512: check-defined-CYCLES \
	$(MLKEM512_DIR)/bin/bench_components_mlkem512
bench_components_768: check-defined-CYCLES \
	$(MLKEM768_DIR)/bin/bench_components_mlkem768
bench_components_1024: check-defined-CYCLES \
	$(MLKEM1024_DIR)/bin/bench_components_mlkem1024
bench_components: bench_components_512 bench_components_768 bench_components_1024

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
