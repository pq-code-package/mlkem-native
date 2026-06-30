# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

FIPS202_SRCS = $(wildcard mlkem/src/fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard mlkem/src/fips202/native/aarch64/src/*.S) \
                        $(wildcard mlkem/src/fips202/native/aarch64/src/*.c) \
                        $(wildcard mlkem/src/fips202/native/x86_64/src/*.c)  \
                        $(wildcard mlkem/src/fips202/native/x86_64/src/*.S)  \
                        $(wildcard mlkem/src/fips202/native/armv81m/src/*.[csS])
endif

SOURCES += $(wildcard mlkem/src/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/src/native/aarch64/src/*.[csS]) \
                   $(wildcard mlkem/src/native/x86_64/src/*.[csS])  \
                   $(wildcard mlkem/src/native/riscv64/src/*.[csS]) \
                   $(wildcard mlkem/src/native/ppc64le/src/*.[csS])
	CFLAGS += -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH \
                  -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
endif

LIB_SRCS := $(SOURCES) $(FIPS202_SRCS)

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

MLKEM512_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR),$(LIB_SRCS))
MLKEM768_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR),$(LIB_SRCS))
MLKEM1024_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR),$(LIB_SRCS))

MLKEM512_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR)/unit,$(LIB_SRCS))
MLKEM768_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR)/unit,$(LIB_SRCS))
MLKEM1024_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR)/unit,$(LIB_SRCS))

MLKEM512_ALLOC_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR)/alloc,$(LIB_SRCS))
MLKEM768_ALLOC_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR)/alloc,$(LIB_SRCS))
MLKEM1024_ALLOC_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR)/alloc,$(LIB_SRCS))

CFLAGS += -Imlkem

$(BUILD_DIR)/libmlkem512.a: $(MLKEM512_OBJS)
$(BUILD_DIR)/libmlkem768.a: $(MLKEM768_OBJS)
$(BUILD_DIR)/libmlkem1024.a: $(MLKEM1024_OBJS)

$(BUILD_DIR)/libmlkem512_unit.a: $(MLKEM512_UNIT_OBJS)
$(BUILD_DIR)/libmlkem768_unit.a: $(MLKEM768_UNIT_OBJS)
$(BUILD_DIR)/libmlkem1024_unit.a: $(MLKEM1024_UNIT_OBJS)

$(BUILD_DIR)/libmlkem512_alloc.a: $(MLKEM512_ALLOC_OBJS)
$(BUILD_DIR)/libmlkem768_alloc.a: $(MLKEM768_ALLOC_OBJS)
$(BUILD_DIR)/libmlkem1024_alloc.a: $(MLKEM1024_ALLOC_OBJS)

$(BUILD_DIR)/libmlkem.a: $(MLKEM512_OBJS) $(MLKEM768_OBJS) $(MLKEM1024_OBJS)

# Generic CFLAGS

$(MLKEM512_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512
$(MLKEM768_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768
$(MLKEM1024_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024

# Lib objects also get the parameter set above; this covers the test entrypoints
# (not in LIB_SRCS) and, for custom builds like Zephyr, every source.
$(MLKEM512_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512
$(MLKEM768_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768
$(MLKEM1024_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024

# Per-test CFLAGS

$(MLKEM512_DIR)/bin/bench_mlkem512: CFLAGS += -Itest/hal
$(MLKEM768_DIR)/bin/bench_mlkem768: CFLAGS += -Itest/hal
$(MLKEM1024_DIR)/bin/bench_mlkem1024: CFLAGS += -Itest/hal

$(MLKEM512_DIR)/bin/bench_components_mlkem512: CFLAGS += -Itest/hal
$(MLKEM768_DIR)/bin/bench_components_mlkem768: CFLAGS += -Itest/hal
$(MLKEM1024_DIR)/bin/bench_components_mlkem1024: CFLAGS += -Itest/hal

$(MLKEM512_DIR)/bin/test_stack512: CFLAGS += -Imlkem/src -fstack-usage
$(MLKEM768_DIR)/bin/test_stack768: CFLAGS += -Imlkem/src -fstack-usage
$(MLKEM1024_DIR)/bin/test_stack1024: CFLAGS += -Imlkem/src -fstack-usage

$(MLKEM512_DIR)/bin/test_unit512: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
$(MLKEM768_DIR)/bin/test_unit768: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
$(MLKEM1024_DIR)/bin/test_unit1024: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes

$(MLKEM512_DIR)/bin/test_alloc512: CFLAGS += -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"
$(MLKEM768_DIR)/bin/test_alloc768: CFLAGS += -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"
$(MLKEM1024_DIR)/bin/test_alloc1024: CFLAGS += -DMLK_CONFIG_FILE=\"../test/configs/test_alloc_config.h\"

define ADD_SOURCE
# Record this binary's test sources -- entrypoint test/$(3)/$(2).c plus extras
# $(4) -- in the per-binary TEST_SRCS. A custom build (CUSTOM_BUILD, see
# test/mk/rules.mk) consumes these directly; a normal build links lib$(1)$(5).a.
$(BUILD_DIR)/$(1)/bin/$(2)$(subst mlkem,,$(1)): TEST_SRCS += test/$(3)/$(2).c $(4)
ifndef CUSTOM_BUILD
$(BUILD_DIR)/$(1)/bin/$(2)$(subst mlkem,,$(1)): LDLIBS += -L$(BUILD_DIR) -l$(1)$(5)
$(BUILD_DIR)/$(1)/bin/$(2)$(subst mlkem,,$(1)): $(BUILD_DIR)/lib$(1)$(5).a
endif
endef

$(foreach scheme,mlkem512 mlkem768 mlkem1024, \
	$(foreach test,$(ACVP_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),acvp)) \
	) \
	$(foreach test,$(WYCHEPROOF_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),wycheproof)) \
	) \
	$(foreach test,$(BENCH_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),bench,test/hal/hal.c)) \
	) \
	$(foreach test,$(BASIC_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test),src)) \
	) \
	$(eval $(call ADD_SOURCE,$(scheme),test_rng_fail,src)) \
	$(eval $(call ADD_SOURCE,$(scheme),test_unit,src,,_unit)) \
	$(eval $(call ADD_SOURCE,$(scheme),test_alloc,src,,_alloc)) \
)

# The set of test binaries, per parameter set.
BINS_512  := $(ALL_TESTS:%=$(MLKEM512_DIR)/bin/%512)
BINS_768  := $(ALL_TESTS:%=$(MLKEM768_DIR)/bin/%768)
BINS_1024 := $(ALL_TESTS:%=$(MLKEM1024_DIR)/bin/%1024)
ALL_BINS  := $(BINS_512) $(BINS_768) $(BINS_1024)

# All tests except rng_fail get notrandombytes (rng_fail provides its own).
$(filter-out %test_rng_fail512 %test_rng_fail768 %test_rng_fail1024,$(ALL_BINS)): \
	TEST_SRCS += test/notrandombytes/notrandombytes.c

# Turn each binary's TEST_SRCS into its prerequisites (via .SECONDEXPANSION, as
# TEST_SRCS is a per-target variable). The scheme's object dir is derived from
# the target ($@ = .../mlkemNNN/bin/foo, so $(@D) sans /bin = .../mlkemNNN).
# Redundant in a normal build (the .a -> .o -> .c chain already implies it), but
# a custom build links the sources directly and so needs them named explicitly.
.SECONDEXPANSION:
ifndef CUSTOM_BUILD
$(ALL_BINS): $$(call MAKE_OBJS,$$(patsubst %/bin,%,$$(@D)),$$(TEST_SRCS))
# EXTRA_SOURCES (platform-specific) is a normal-build feature: its per-file
# CFLAGS only attach to object targets, which custom builds don't produce, so a
# custom-build platform handles its own extra sources in its CUSTOM_BUILD recipe.
$(ALL_BINS): TEST_SRCS += $(EXTRA_SOURCES)
ifneq ($(EXTRA_SOURCES),)
$(call MAKE_OBJS, $(MLKEM512_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
$(call MAKE_OBJS, $(MLKEM768_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
$(call MAKE_OBJS, $(MLKEM1024_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
endif
else
$(ALL_BINS): $$(TEST_SRCS) $(LIB_SRCS)
# Extra per-binary prerequisites a custom-build platform needs (e.g. Zephyr's
# app inputs and active-target marker, set in test/zephyr/platform.mk).
$(ALL_BINS): $(CUSTOM_BUILD_DEPS)
endif

# ABI checker
ABICHECK_DIR = $(BUILD_DIR)/abicheck

# Map $(ARCH) to the abicheck per-arch subdir name. For most architectures
# the subdir matches $(ARCH); two exceptions:
#   - arm-none-eabi- targets: $(ARCH) = arm (a generic label for the
#     bare-metal Cortex-M family). The abicheck subdir is the more specific
#     armv81m.
#   - PPC64LE targets: $(ARCH) = powerpc64le (matches uname -m / Debian
#     toolchain prefix). The abicheck subdir is ppc64le, matching the C
#     symbol naming (asm_call_stub_ppc64le, struct ppc64le_register_state).
ifeq ($(ARCH),arm)
ABICHECK_ARCH := armv81m
else ifeq ($(ARCH),powerpc64le)
ABICHECK_ARCH := ppc64le
else
ABICHECK_ARCH := $(ARCH)
endif

ABICHECK_SOURCES = test/abicheck/abicheck.c test/abicheck/selftest.c
ABICHECK_SOURCES += $(wildcard test/abicheck/$(ABICHECK_ARCH)/abicheck_$(ABICHECK_ARCH).c)
ABICHECK_SOURCES += $(wildcard test/abicheck/$(ABICHECK_ARCH)/callstub_$(ABICHECK_ARCH).S)
ABICHECK_SOURCES += $(wildcard test/abicheck/$(ABICHECK_ARCH)/selftest_$(ABICHECK_ARCH).S)
ABICHECK_SOURCES += $(wildcard test/abicheck/$(ABICHECK_ARCH)/checks/check_*.c)
ABICHECK_SOURCES += $(wildcard test/notrandombytes/*.c)

# Per-arch shipped assembly (mlkem/src/.../*.S), assembled directly with
# ABICHECK_ASM_CFLAGS (defined below).
ifeq ($(ABICHECK_ARCH),aarch64)
ABICHECK_ASM_SOURCES := $(wildcard mlkem/src/native/aarch64/src/*.S) \
                        $(wildcard mlkem/src/fips202/native/aarch64/src/*.S)
else ifeq ($(ABICHECK_ARCH),x86_64)
ABICHECK_ASM_SOURCES := $(wildcard mlkem/src/native/x86_64/src/*.S) \
                        $(wildcard mlkem/src/fips202/native/x86_64/src/*.S)
else ifeq ($(ABICHECK_ARCH),ppc64le)
ABICHECK_ASM_SOURCES := $(wildcard mlkem/src/native/ppc64le/src/*.S)
else ifeq ($(ABICHECK_ARCH),armv81m)
ABICHECK_ASM_SOURCES := $(wildcard mlkem/src/fips202/native/armv81m/src/*.S)
else
ABICHECK_ASM_SOURCES :=
endif

# Per-capability CFLAGS injection (e.g. -march=armv8.4-a+sha3 for SHA3,
# -mavx2 -mbmi2 for AVX2), generated by scripts/autogen from each kernel's
# YAML 'ABI.Features:' list. abicheck.mk includes the per-arch abicheck_<arch>.mk.
include test/abicheck/abicheck.mk

# SHA3-not-assemblable case: some aarch64 compilers do not support
# `-march=armv8.4-a+sha3`, in which case we cannot even assemble the SHA3
# Keccak kernels.
ifeq ($(ARCH),aarch64)
ifneq ($(MK_COMPILER_SUPPORTS_SHA3),1)
ABICHECK_ASM_SOURCES := $(filter-out $(ABICHECK_REQ_SHA3_FILES),$(ABICHECK_ASM_SOURCES))
endif
endif

ABICHECK_ALL_SOURCES = $(ABICHECK_SOURCES) $(ABICHECK_ASM_SOURCES)
ABICHECK_OBJS = $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_ALL_SOURCES))

# Predefine the kernel-gating macros (arith backend, fips202 NEED_*, MLKEM_K)
# so the shipped #ifs evaluate true. Undefine the two USE_NATIVE_BACKEND
# switches so common.h does not pull in the per-arch backend headers and the
# constant-table C declarations the abicheck does not link against.
ABICHECK_ASM_CFLAGS := \
  -UMLK_CONFIG_USE_NATIVE_BACKEND_ARITH \
  -UMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202 \
  -DMLK_CONFIG_MULTILEVEL_WITH_SHARED \
  -DMLK_CONFIG_PARAMETER_SET=768 \
  -DMLK_CONFIG_NAMESPACE_PREFIX=mlk \
  -DMLK_ARITH_BACKEND_AARCH64 \
  -DMLK_ARITH_BACKEND_PPC64LE_DEFAULT \
  -DMLK_ARITH_BACKEND_X86_64_DEFAULT \
  -DMLK_FIPS202_AARCH64_NEED_X1_SCALAR \
  -DMLK_FIPS202_AARCH64_NEED_X1_V84A \
  -DMLK_FIPS202_AARCH64_NEED_X2_V84A \
  -DMLK_FIPS202_AARCH64_NEED_X4_V8A_SCALAR_HYBRID \
  -DMLK_FIPS202_AARCH64_NEED_X4_V8A_V84A_SCALAR_HYBRID \
  -DMLK_FIPS202_ARMV81M_NEED_X4 \
  -DMLK_FIPS202_X86_64_NEED_X4_AVX2

ABICHECK_ASM_OBJS = $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_ASM_SOURCES))
$(ABICHECK_ASM_OBJS): CFLAGS += $(ABICHECK_ASM_CFLAGS)

# Platform support objects (e.g. the bare-metal startup providing _start and the
# semihosting runtime). EXTRA_SOURCES is set by a platform makefile (see
# test/baremetal/platform/*/platform.mk via EXTRA_MAKEFILE); empty for native
# builds. Like the other test binaries, the ABI checker must link these or it has
# no entry point on bare metal. The platform's LDSCRIPT is already applied via
# LDFLAGS in the link rule.
ABICHECK_EXTRA_OBJS = $(call MAKE_OBJS,$(ABICHECK_DIR),$(EXTRA_SOURCES))
ifneq ($(EXTRA_SOURCES),)
$(ABICHECK_EXTRA_OBJS): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
endif

$(ABICHECK_DIR)/bin/abicheck: $(ABICHECK_OBJS) $(ABICHECK_EXTRA_OBJS)
