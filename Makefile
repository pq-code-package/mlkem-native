# SPDX-License-Identifier: Apache-2.0

.PHONY: func kat nistkat acvp \
	run_func run_kat run_nistkat run_acvp \
	buildall checkall all 			      \
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

run_kat: kat
	$(MLKEM512_DIR)/bin/gen_KAT512   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  kat-sha256
	$(MLKEM768_DIR)/bin/gen_KAT768   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  kat-sha256
	$(MLKEM1024_DIR)/bin/gen_KAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024 kat-sha256

run_nistkat: nistkat
	$(MLKEM512_DIR)/bin/gen_NISTKAT512   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  nistkat-sha256
	$(MLKEM768_DIR)/bin/gen_NISTKAT768   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  nistkat-sha256
	$(MLKEM1024_DIR)/bin/gen_NISTKAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024 nistkat-sha256

run_func: func
	$(MLKEM512_DIR)/bin/test_mlkem512
	$(MLKEM768_DIR)/bin/test_mlkem768
	$(MLKEM1024_DIR)/bin/test_mlkem1024

run_acvp: acvp
	python3 ./test/acvp_client.py

lib: $(BUILD_DIR)/libmlkem.a

# Enforce setting CYCLES make variable when
# building benchmarking binaries
check_defined = $(if $(value $1),, $(error $2))
check-defined-CYCLES:
	@:$(call check_defined,CYCLES,CYCLES undefined. Benchmarking requires setting one of NO PMU PERF M1)

bench: check-defined-CYCLES \
	$(MLKEM512_DIR)/bin/bench_mlkem512 \
	$(MLKEM768_DIR)/bin/bench_mlkem768 \
	$(MLKEM1024_DIR)/bin/bench_mlkem1024

func: \
  $(MLKEM512_DIR)/bin/test_mlkem512 \
  $(MLKEM768_DIR)/bin/test_mlkem768 \
  $(MLKEM1024_DIR)/bin/test_mlkem1024

acvp: \
	$(MLKEM512_DIR)/bin/acvp_mlkem512 \
	$(MLKEM768_DIR)/bin/acvp_mlkem768 \
	$(MLKEM1024_DIR)/bin/acvp_mlkem1024

bench_components: check-defined-CYCLES \
	$(MLKEM512_DIR)/bin/bench_components_mlkem512 \
	$(MLKEM768_DIR)/bin/bench_components_mlkem768 \
	$(MLKEM1024_DIR)/bin/bench_components_mlkem1024

nistkat: \
	$(MLKEM512_DIR)/bin/gen_NISTKAT512 \
	$(MLKEM768_DIR)/bin/gen_NISTKAT768 \
	$(MLKEM1024_DIR)/bin/gen_NISTKAT1024

kat: \
	$(MLKEM512_DIR)/bin/gen_KAT512 \
	$(MLKEM768_DIR)/bin/gen_KAT768 \
	$(MLKEM1024_DIR)/bin/gen_KAT1024

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
