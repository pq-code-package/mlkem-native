# SPDX-License-Identifier: Apache-2.0

.PHONY: build_func build_kat build_nistkat build_acvp \
	check_func check_kat check_nistkat check_acvp \
	buildall checkall all 			      \
	clean quickcheck check-defined-CYCLES

.DEFAULT_GOAL := buildall
all: quickcheck

include mk/config.mk
-include mk/$(MAKECMDGOALS).mk
include mk/crypto.mk
include mk/schemes.mk
include mk/rules.mk

quickcheck: checkall

buildall: build_func build_nistkat build_kat build_acvp
	$(Q)echo "  Everything builds fine!"

checkall: check_kat check_nistkat check_func check_acvp
	$(Q)echo "  Everything checks fine!"

check_kat_512: build_kat_512
	$(MLKEM512_DIR)/bin/gen_KAT512 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  kat-sha256
check_kat_768: build_kat_768
	$(MLKEM768_DIR)/bin/gen_KAT768 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  kat-sha256
check_kat_1024: build_kat_1024
	$(MLKEM1024_DIR)/bin/gen_KAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024  kat-sha256
check_kat: check_kat_512 check_kat_768 check_kat_1024

check_nistkat_512: build_nistkat_512
	$(MLKEM512_DIR)/bin/gen_NISTKAT512 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  nistkat-sha256
check_nistkat_768: build_nistkat_768
	$(MLKEM768_DIR)/bin/gen_NISTKAT768 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  nistkat-sha256
check_nistkat_1024: build_nistkat_1024
	$(MLKEM1024_DIR)/bin/gen_NISTKAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024  nistkat-sha256
check_nistkat: check_nistkat_512 check_nistkat_768 check_nistkat_1024

check_func_512: build_func_512
	$(MLKEM512_DIR)/bin/test_mlkem512
check_func_768: build_func_768
	$(MLKEM768_DIR)/bin/test_mlkem768
check_func_1024: build_func_1024
	$(MLKEM1024_DIR)/bin/test_mlkem1024
check_func: check_func_512 check_func_768 check_func_1024

check_acvp: build_acvp
	python3 ./test/acvp_client.py

build_func_512:  $(MLKEM512_DIR)/bin/test_mlkem512
build_func_768:  $(MLKEM768_DIR)/bin/test_mlkem768
build_func_1024: $(MLKEM1024_DIR)/bin/test_mlkem1024
build_func: build_func_512 build_func_768 build_func_1024

build_nistkat_512: $(MLKEM512_DIR)/bin/gen_NISTKAT512
build_nistkat_768: $(MLKEM768_DIR)/bin/gen_NISTKAT768
build_nistkat_1024: $(MLKEM1024_DIR)/bin/gen_NISTKAT1024
build_nistkat: build_nistkat_512 build_nistkat_768 build_nistkat_1024

build_kat_512: $(MLKEM512_DIR)/bin/gen_KAT512
build_kat_768: $(MLKEM768_DIR)/bin/gen_KAT768
build_kat_1024: $(MLKEM1024_DIR)/bin/gen_KAT1024
build_kat: build_kat_512 build_kat_768 build_kat_1024

build_acvp_512:  $(MLKEM512_DIR)/bin/acvp_mlkem512
build_acvp_768:  $(MLKEM768_DIR)/bin/acvp_mlkem768
build_acvp_1024: $(MLKEM1024_DIR)/bin/acvp_mlkem1024
build_acvp: build_acvp_512 build_acvp_768 build_acvp_1024

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

bench_components: check-defined-CYCLES \
	$(MLKEM512_DIR)/bin/bench_components_mlkem512 \
	$(MLKEM768_DIR)/bin/bench_components_mlkem768 \
	$(MLKEM1024_DIR)/bin/bench_components_mlkem1024

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
