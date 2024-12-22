# SPDX-License-Identifier: Apache-2.0

.PHONY: mlkem kat nistkat clean quickcheck buildall checkall all
.DEFAULT_GOAL := buildall
all: quickcheck

include mk/config.mk
-include mk/$(MAKECMDGOALS).mk
include mk/crypto.mk
include mk/schemes.mk
include mk/rules.mk

# Binary wrapper, e.g. qemu-aarch64/qemu-x86_64 for emulation.
# Usually chosen consistently with CROSS_PREFIX for compilation.
WRAP?=

quickcheck: checkall

buildall: mlkem nistkat kat acvp
	$(Q)echo "  Everything builds fine!"

checkall: buildall check_kat check_nistkat check_func check_acvp
	$(Q)echo "  Everything checks fine!"

check_kat: buildall
	$(WRAP) $(MLKEM512_DIR)/bin/gen_KAT512   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  kat-sha256
	$(WRAP) $(MLKEM768_DIR)/bin/gen_KAT768   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  kat-sha256
	$(WRAP) $(MLKEM1024_DIR)/bin/gen_KAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024 kat-sha256

check_nistkat: buildall
	$(WRAP) $(MLKEM512_DIR)/bin/gen_NISTKAT512   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-512  nistkat-sha256
	$(WRAP) $(MLKEM768_DIR)/bin/gen_NISTKAT768   | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-768  nistkat-sha256
	$(WRAP) $(MLKEM1024_DIR)/bin/gen_NISTKAT1024 | sha256sum | cut -d " " -f 1 | xargs ./META.sh ML-KEM-1024 nistkat-sha256

check_func: buildall
	$(WRAP) $(MLKEM512_DIR)/bin/test_mlkem512
	$(WRAP) $(MLKEM768_DIR)/bin/test_mlkem768
	$(WRAP) $(MLKEM1024_DIR)/bin/test_mlkem1024

check_acvp: buildall
	python3 ./test/acvp_client.py

lib: $(BUILD_DIR)/libmlkem.a

mlkem: \
  $(MLKEM512_DIR)/bin/test_mlkem512 \
  $(MLKEM768_DIR)/bin/test_mlkem768 \
  $(MLKEM1024_DIR)/bin/test_mlkem1024

bench: \
	$(MLKEM512_DIR)/bin/bench_mlkem512 \
	$(MLKEM768_DIR)/bin/bench_mlkem768 \
	$(MLKEM1024_DIR)/bin/bench_mlkem1024

acvp: \
	$(MLKEM512_DIR)/bin/acvp_mlkem512 \
	$(MLKEM768_DIR)/bin/acvp_mlkem768 \
	$(MLKEM1024_DIR)/bin/acvp_mlkem1024

bench_components: \
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

# emulate ARM64 binary on x86_64 machine
emulate:
	$(Q)$(MAKE) --quiet CROSS_PREFIX=aarch64-none-linux-gnu- $(TARGET)
	$(Q)$(QEMU) $(TARGET)

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
