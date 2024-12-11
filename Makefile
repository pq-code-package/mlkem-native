# SPDX-License-Identifier: Apache-2.0

.PHONY: mlkem kat nistkat clean quickcheck buildall all
.DEFAULT_GOAL := buildall
all: quickcheck

include mk/config.mk
-include mk/$(MAKECMDGOALS).mk
include mk/crypto.mk
include mk/schemes.mk
include mk/rules.mk

buildall: mlkem nistkat kat acvp
	$(Q)echo "  Everything builds fine!"

quickcheck: buildall
	# Run basic functionality checks
	$(MLKEM512_DIR)/bin/test_mlkem512
	$(MLKEM768_DIR)/bin/test_mlkem768
	$(MLKEM1024_DIR)/bin/test_mlkem1024
	./scripts/acvp
	$(Q)echo "  Functionality and ACVP tests passed!"

lib: \
  $(BUILD_DIR)/libmlkem.a

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
