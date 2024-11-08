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
	$(MLKEM512_BUILD_DIR)/bin/test_mlkem512_$(OPT_SUFFIX)
	$(MLKEM768_BUILD_DIR)/bin/test_mlkem768_$(OPT_SUFFIX)
	$(MLKEM1024_BUILD_DIR)/bin/test_mlkem1024_$(OPT_SUFFIX)
	./scripts/tests acvp --opt=$(OPT_SUFFIX)
	$(Q)echo "  Functionality and ACVP tests passed!"

mlkem: \
  $(MLKEM512_BUILD_DIR)/bin/test_mlkem512_$(OPT_SUFFIX) \
  $(MLKEM768_BUILD_DIR)/bin/test_mlkem768_$(OPT_SUFFIX) \
  $(MLKEM1024_BUILD_DIR)/bin/test_mlkem1024_$(OPT_SUFFIX)

bench: \
	$(MLKEM512_BUILD_DIR)/bin/bench_mlkem512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/bench_mlkem768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/bench_mlkem1024_$(OPT_SUFFIX)

acvp: \
	$(MLKEM512_BUILD_DIR)/bin/acvp_mlkem512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/acvp_mlkem768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/acvp_mlkem1024_$(OPT_SUFFIX)

bench_components: \
	$(MLKEM512_BUILD_DIR)/bin/bench_components_mlkem512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/bench_components_mlkem768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/bench_components_mlkem1024_$(OPT_SUFFIX)

nistkat: \
	$(MLKEM512_BUILD_DIR)/bin/gen_NISTKAT512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/gen_NISTKAT768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/gen_NISTKAT1024_$(OPT_SUFFIX)

kat: \
  $(MLKEM512_BUILD_DIR)/bin/gen_KAT512_$(OPT_SUFFIX) \
  $(MLKEM768_BUILD_DIR)/bin/gen_KAT768_$(OPT_SUFFIX) \
  $(MLKEM1024_BUILD_DIR)/bin/gen_KAT1024_$(OPT_SUFFIX)

# emulate ARM64 binary on x86_64 machine
emulate:
	$(Q)$(MAKE) --quiet CROSS_PREFIX=aarch64-none-linux-gnu- $(TARGET)
	$(Q)$(QEMU) $(TARGET)

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
