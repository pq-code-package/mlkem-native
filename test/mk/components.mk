# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

FIPS202_SRCS = $(wildcard mlkem/src/fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard mlkem/src/fips202/native/aarch64/src/*.S) $(wildcard mlkem/src/fips202/native/aarch64/src/*.c) $(wildcard mlkem/src/fips202/native/x86_64/src/*.c) $(wildcard mlkem/src/fips202/native/x86_64/src/*.S) $(wildcard mlkem/src/fips202/native/armv81m/src/*.[csS])
endif

SOURCES += $(wildcard mlkem/src/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/src/native/aarch64/src/*.[csS]) $(wildcard mlkem/src/native/x86_64/src/*.[csS]) $(wildcard mlkem/src/native/riscv64/src/*.[csS]) $(wildcard mlkem/src/native/ppc64le/src/*.[csS])
	CFLAGS += -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
endif

BASIC_TESTS = test_mlkem gen_KAT test_stack
ACVP_TESTS = acvp_mlkem
WYCHEPROOF_TESTS = wycheproof_mlkem
BENCH_TESTS = bench_mlkem bench_components_mlkem
UNIT_TESTS = test_unit
ALLOC_TESTS = test_alloc
RNG_FAIL_TESTS = test_rng_fail
ALL_TESTS = $(BASIC_TESTS) $(ACVP_TESTS) $(WYCHEPROOF_TESTS) $(BENCH_TESTS) $(UNIT_TESTS) $(ALLOC_TESTS) $(RNG_FAIL_TESTS)

MLKEM512_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_DIR = $(BUILD_DIR)/mlkem1024

MLKEM512_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLKEM512_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512
MLKEM768_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLKEM768_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768
MLKEM1024_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLKEM1024_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024

# Unit test object files - same sources but with MLK_STATIC_TESTABLE=
UNIT_CFLAGS = -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes

MLKEM512_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR)/unit,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM512_UNIT_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512 $(UNIT_CFLAGS)
MLKEM768_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR)/unit,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM768_UNIT_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768 $(UNIT_CFLAGS)
MLKEM1024_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR)/unit,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM1024_UNIT_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024 $(UNIT_CFLAGS)

# Alloc test object files - same sources but with custom alloc config
MLKEM512_ALLOC_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR)/alloc,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM512_ALLOC_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512 -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"
MLKEM768_ALLOC_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR)/alloc,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM768_ALLOC_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768 -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"
MLKEM1024_ALLOC_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR)/alloc,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM1024_ALLOC_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024 -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"

CFLAGS += -Imlkem

$(BUILD_DIR)/libmlkem512.a: $(MLKEM512_OBJS)
$(BUILD_DIR)/libmlkem768.a: $(MLKEM768_OBJS)
$(BUILD_DIR)/libmlkem1024.a: $(MLKEM1024_OBJS)

# Unit libraries with exposed internal functions
$(BUILD_DIR)/libmlkem512_unit.a: $(MLKEM512_UNIT_OBJS)
$(BUILD_DIR)/libmlkem768_unit.a: $(MLKEM768_UNIT_OBJS)
$(BUILD_DIR)/libmlkem1024_unit.a: $(MLKEM1024_UNIT_OBJS)

# Alloc test libraries with custom alloc config
$(BUILD_DIR)/libmlkem512_alloc.a: $(MLKEM512_ALLOC_OBJS)
$(BUILD_DIR)/libmlkem768_alloc.a: $(MLKEM768_ALLOC_OBJS)
$(BUILD_DIR)/libmlkem1024_alloc.a: $(MLKEM1024_ALLOC_OBJS)

$(BUILD_DIR)/libmlkem.a: $(MLKEM512_OBJS) $(MLKEM768_OBJS) $(MLKEM1024_OBJS)

$(MLKEM512_DIR)/bin/bench_mlkem512: CFLAGS += -Itest/hal
$(MLKEM768_DIR)/bin/bench_mlkem768: CFLAGS += -Itest/hal
$(MLKEM1024_DIR)/bin/bench_mlkem1024: CFLAGS += -Itest/hal
$(MLKEM512_DIR)/bin/bench_components_mlkem512: CFLAGS += -Itest/hal
$(MLKEM768_DIR)/bin/bench_components_mlkem768: CFLAGS += -Itest/hal
$(MLKEM1024_DIR)/bin/bench_components_mlkem1024: CFLAGS += -Itest/hal

$(MLKEM512_DIR)/bin/test_stack512: CFLAGS += -Imlkem/src -fstack-usage
$(MLKEM768_DIR)/bin/test_stack768: CFLAGS += -Imlkem/src -fstack-usage
$(MLKEM1024_DIR)/bin/test_stack1024: CFLAGS += -Imlkem/src -fstack-usage

$(MLKEM512_DIR)/test/src/test_alloc.c.o: CFLAGS += -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"
$(MLKEM768_DIR)/test/src/test_alloc.c.o: CFLAGS += -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"
$(MLKEM1024_DIR)/test/src/test_alloc.c.o: CFLAGS += -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"

$(MLKEM512_DIR)/test/src/test_unit.c.o: CFLAGS += $(UNIT_CFLAGS)
$(MLKEM768_DIR)/test/src/test_unit.c.o: CFLAGS += $(UNIT_CFLAGS)
$(MLKEM1024_DIR)/test/src/test_unit.c.o: CFLAGS += $(UNIT_CFLAGS)

$(MLKEM512_DIR)/bin/test_unit512: CFLAGS += $(UNIT_CFLAGS)
$(MLKEM768_DIR)/bin/test_unit768: CFLAGS += $(UNIT_CFLAGS)
$(MLKEM1024_DIR)/bin/test_unit1024: CFLAGS += $(UNIT_CFLAGS)

# Unit library object files compiled with MLK_STATIC_TESTABLE=
$(MLKEM512_DIR)/unit_%: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
$(MLKEM768_DIR)/unit_%: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
$(MLKEM1024_DIR)/unit_%: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes

$(MLKEM512_DIR)/bin/bench_mlkem512: $(MLKEM512_DIR)/test/hal/hal.c.o
$(MLKEM768_DIR)/bin/bench_mlkem768: $(MLKEM768_DIR)/test/hal/hal.c.o
$(MLKEM1024_DIR)/bin/bench_mlkem1024: $(MLKEM1024_DIR)/test/hal/hal.c.o
$(MLKEM512_DIR)/bin/bench_components_mlkem512: $(MLKEM512_DIR)/test/hal/hal.c.o
$(MLKEM768_DIR)/bin/bench_components_mlkem768: $(MLKEM768_DIR)/test/hal/hal.c.o
$(MLKEM1024_DIR)/bin/bench_components_mlkem1024: $(MLKEM1024_DIR)/test/hal/hal.c.o

$(MLKEM512_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512
$(MLKEM768_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768
$(MLKEM1024_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024

# Link tests with respective library (except test_unit which includes sources directly)
define ADD_SOURCE
$(BUILD_DIR)/$(1)/bin/$(2)$(subst mlkem,,$(1)): LDLIBS += -L$(BUILD_DIR) -l$(1)
$(BUILD_DIR)/$(1)/bin/$(2)$(subst mlkem,,$(1)): $(BUILD_DIR)/$(1)/test/$(3)/$(2).c.o $(BUILD_DIR)/lib$(1).a
endef

# Special rule for test_unit - link against unit libraries with exposed internal functions
define ADD_SOURCE_UNIT
$(BUILD_DIR)/$(1)/bin/test_unit$(subst mlkem,,$(1)): LDLIBS += -L$(BUILD_DIR) -l$(1)_unit
$(BUILD_DIR)/$(1)/bin/test_unit$(subst mlkem,,$(1)): $(BUILD_DIR)/$(1)/test/src/test_unit.c.o $(BUILD_DIR)/lib$(1)_unit.a $(call MAKE_OBJS, $(BUILD_DIR)/$(1), $(wildcard test/notrandombytes/*.c))
endef

# Special rule for test_alloc - link against alloc libraries with custom alloc config
define ADD_SOURCE_ALLOC
$(BUILD_DIR)/$(1)/bin/test_alloc$(subst mlkem,,$(1)): LDLIBS += -L$(BUILD_DIR) -l$(1)_alloc
$(BUILD_DIR)/$(1)/bin/test_alloc$(subst mlkem,,$(1)): $(BUILD_DIR)/$(1)/test/src/test_alloc.c.o $(BUILD_DIR)/lib$(1)_alloc.a $(call MAKE_OBJS, $(BUILD_DIR)/$(1), $(wildcard test/notrandombytes/*.c))
endef

$(foreach scheme,mlkem512 mlkem768 mlkem1024, \
	$(foreach test,$(ACVP_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),acvp)) \
	) \
	$(foreach test,$(WYCHEPROOF_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),wycheproof)) \
	) \
	$(foreach test,$(BENCH_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),bench)) \
	) \
	$(foreach test,$(BASIC_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),src)) \
	) \
	$(eval $(call ADD_SOURCE,$(scheme),test_rng_fail,src)) \
	$(eval $(call ADD_SOURCE_UNIT,$(scheme))) \
	$(eval $(call ADD_SOURCE_ALLOC,$(scheme))) \
)

# All tests get EXTRA_SOURCES
$(ALL_TESTS:%=$(MLKEM512_DIR)/bin/%512): $(call MAKE_OBJS, $(MLKEM512_DIR), $(EXTRA_SOURCES))
$(ALL_TESTS:%=$(MLKEM768_DIR)/bin/%768): $(call MAKE_OBJS, $(MLKEM768_DIR), $(EXTRA_SOURCES))
$(ALL_TESTS:%=$(MLKEM1024_DIR)/bin/%1024): $(call MAKE_OBJS, $(MLKEM1024_DIR), $(EXTRA_SOURCES))

# All tests except rng_fail get notrandombytes (rng_fail provides its own)
$(filter-out %test_rng_fail512,$(ALL_TESTS:%=$(MLKEM512_DIR)/bin/%512)): $(call MAKE_OBJS, $(MLKEM512_DIR), $(wildcard test/notrandombytes/*.c))
$(filter-out %test_rng_fail768,$(ALL_TESTS:%=$(MLKEM768_DIR)/bin/%768)): $(call MAKE_OBJS, $(MLKEM768_DIR), $(wildcard test/notrandombytes/*.c))
$(filter-out %test_rng_fail1024,$(ALL_TESTS:%=$(MLKEM1024_DIR)/bin/%1024)): $(call MAKE_OBJS, $(MLKEM1024_DIR), $(wildcard test/notrandombytes/*.c))

# Apply EXTRA_CFLAGS to EXTRA_SOURCES object files
ifneq ($(EXTRA_SOURCES),)
$(call MAKE_OBJS, $(MLKEM512_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
$(call MAKE_OBJS, $(MLKEM768_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
$(call MAKE_OBJS, $(MLKEM1024_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
endif

# ABI checker
ABICHECK_DIR = $(BUILD_DIR)/abicheck

ABICHECK_SOURCES = test/abicheck/abicheck.c test/abicheck/abicheckutil.c
ABICHECK_SOURCES += test/abicheck/aarch64_callstub.S test/abicheck/x86_64_callstub.S
ABICHECK_SOURCES += $(wildcard test/abicheck/check_*.c)
ABICHECK_SOURCES += $(wildcard test/notrandombytes/*.c)

# The assembly under test is exported in standalone, guard-free form into
# test/abicheck/asm/<arch>/ by scripts/autogen. These files have no #include
# and no preprocessor guards, and their global symbols are already namespaced
# to mlk_*, so the ABI checker assembles them directly - no backends.h shim, no
# backend-selection defines, no constant-data C files.
ABICHECK_ASM_SOURCES = $(wildcard test/abicheck/asm/$(ARCH)/*.S)

# Because the exported assembly is guard-free, the SHA3-dependent AArch64 Keccak
# variants (v84a) now carry their eor3/rax1/... instructions unconditionally,
# whereas the dev sources gate them behind __ARM_FEATURE_SHA3. The generated
# check_*.c files keep that same #if defined(__ARM_FEATURE_SHA3) guard, so a
# check references its assembly symbol exactly when the compiler has SHA3 in
# effect. Gate the assembly inclusion on the very same predefine - tested under
# the actual CFLAGS the checks are compiled with - so the two never disagree
# (auto.mk adds -march=...+sha3 to CFLAGS when supported, and some compilers,
# e.g. Apple clang on Apple silicon, predefine __ARM_FEATURE_SHA3 regardless).
ifeq ($(ARCH),aarch64)
MK_ABICHECK_FEATURE_SHA3 := $(shell echo | $(CC) $(CFLAGS) -dM -E -x c - 2>/dev/null | grep -c __ARM_FEATURE_SHA3)
ifeq ($(MK_ABICHECK_FEATURE_SHA3),0)
# filter-out allows only a single % wildcard, so 'v84a' appearing mid-name is
# matched with foreach/findstring instead.
ABICHECK_ASM_SOURCES := $(foreach f,$(ABICHECK_ASM_SOURCES),$(if $(findstring v84a,$(f)),,$(f)))
endif
endif

ABICHECK_ALL_SOURCES = $(ABICHECK_SOURCES) $(ABICHECK_ASM_SOURCES)
ABICHECK_OBJS = $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_ALL_SOURCES))

# The driver and check C files include mlkem/src/sys.h and common.h, which need
# a namespace prefix and parameter set. The exported assembly needs neither.
$(ABICHECK_OBJS): CFLAGS += -DMLK_CONFIG_NAMESPACE_PREFIX=mlk
$(ABICHECK_OBJS): CFLAGS += -DMLK_CONFIG_MULTILEVEL_WITH_SHARED

ifeq ($(ARCH),x86_64)
$(ABICHECK_OBJS): CFLAGS += -mavx2 -mbmi2
endif

$(ABICHECK_DIR)/bin/abicheck: $(ABICHECK_OBJS)
