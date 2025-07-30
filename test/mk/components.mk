# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

FIPS202_SRCS = $(wildcard mlkem/src/fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard mlkem/src/fips202/native/aarch64/src/*.S) $(wildcard mlkem/src/fips202/native/aarch64/src/*.c) $(wildcard mlkem/src/fips202/native/x86_64/src/*.c)
endif

SOURCES += $(wildcard mlkem/src/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/src/native/aarch64/src/*.[csS]) $(wildcard mlkem/src/native/x86_64/src/*.[csS])
	CFLAGS += -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
endif

ALL_TESTS = test_mlkem acvp_mlkem bench_mlkem bench_components_mlkem gen_KAT test_stack

MLKEM512_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_DIR = $(BUILD_DIR)/mlkem1024

MLKEM512_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLKEM512_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512
MLKEM768_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLKEM768_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768
MLKEM1024_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR),$(SOURCES) $(FIPS202_SRCS))
$(MLKEM1024_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024




$(BUILD_DIR)/libmlkem512.a: $(MLKEM512_OBJS)
$(BUILD_DIR)/libmlkem768.a: $(MLKEM768_OBJS)
$(BUILD_DIR)/libmlkem1024.a: $(MLKEM1024_OBJS)

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

$(MLKEM512_DIR)/bin/bench_mlkem512: $(MLKEM512_DIR)/test/hal/hal.c.o
$(MLKEM768_DIR)/bin/bench_mlkem768: $(MLKEM768_DIR)/test/hal/hal.c.o
$(MLKEM1024_DIR)/bin/bench_mlkem1024: $(MLKEM1024_DIR)/test/hal/hal.c.o
$(MLKEM512_DIR)/bin/bench_components_mlkem512: $(MLKEM512_DIR)/test/hal/hal.c.o
$(MLKEM768_DIR)/bin/bench_components_mlkem768: $(MLKEM768_DIR)/test/hal/hal.c.o
$(MLKEM1024_DIR)/bin/bench_components_mlkem1024: $(MLKEM1024_DIR)/test/hal/hal.c.o

$(MLKEM512_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512
$(MLKEM768_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768
$(MLKEM1024_DIR)/bin/%: CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024

# Link tests with respective library
define ADD_SOURCE
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): LDLIBS += -L$(BUILD_DIR) -l$(1)
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): $(BUILD_DIR)/$(1)/test/$(2).c.o $(BUILD_DIR)/lib$(1).a
endef

$(foreach scheme,mlkem512 mlkem768 mlkem1024, \
	$(foreach test,$(ALL_TESTS), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test))) \
	) \
)

$(ALL_TESTS:%=$(MLKEM512_DIR)/bin/%512): $(call MAKE_OBJS, $(MLKEM512_DIR), $(wildcard test/notrandombytes/*.c))
$(ALL_TESTS:%=$(MLKEM768_DIR)/bin/%768): $(call MAKE_OBJS, $(MLKEM768_DIR), $(wildcard test/notrandombytes/*.c))
$(ALL_TESTS:%=$(MLKEM1024_DIR)/bin/%1024): $(call MAKE_OBJS, $(MLKEM1024_DIR), $(wildcard test/notrandombytes/*.c))

ABICHECK_DIR = $(BUILD_DIR)/abicheck

# ABI checker sources
ABICHECK_SOURCES = test/abicheck/abicheck.c test/abicheck/abicheckutil.c test/abicheck/aarch64_callstub.S
ABICHECK_SOURCES += $(wildcard test/abicheck/check_*.c)
ABICHECK_SOURCES += $(wildcard test/notrandombytes/*.c)

# Assembly sources for the functions under test (only aarch64 for now)
# Only include AArch64 assembly sources on AArch64 platforms
ABICHECK_ASM_SOURCES =

ifeq ($(IS_AARCH64),1)
	ABICHECK_ASM_SOURCES += $(wildcard mlkem/src/fips202/native/aarch64/src/*.S)
	ABICHECK_ASM_SOURCES += $(wildcard mlkem/src/native/aarch64/src/*.S)
else ifeq ($(IS_X86_64),1)
# NOTE: We need this even though the ABI checker is currently AArch64 only,
# as common.h pulls in the backend.
	ABICHECK_ASM_SOURCES += $(wildcard mlkem/src/fips202/native/x86_64/src/*.S)
	ABICHECK_ASM_SOURCES += $(wildcard mlkem/src/native/x86_64/src/*.S)
endif

# All ABI checker sources
ABICHECK_ALL_SOURCES = $(ABICHECK_SOURCES) $(ABICHECK_ASM_SOURCES)

# ABI checker objects
ABICHECK_OBJS = $(call MAKE_OBJS,$(ABICHECK_DIR),$(ABICHECK_ALL_SOURCES))

$(ABICHECK_OBJS): CFLAGS += -DMLK_CONFIG_NAMESPACE_PREFIX=mlk

# The hackery below is to work around the preprocessor guards in the ASM files.
# TODO: We should really be working with 'raw' ASM files without guards.
ifeq ($(IS_AARCH64),1)
# The ASM files pull in common.h, which pulls in the backend meta files if
# MLK_CONFIG_USE_NATIVE_BACKEND_XXX is set. This, in turn, selects a subset
# of MLK_FIPS202_AARCH64_NEED_XXX via `#define ...` in the source, conflicting
# with us setting all of them below using `-D...` which leads to `#define .. 1`.
# To work around, we disable the backends in the config but explicitly enable
# the directives that guard the ASM files. Again, this is hacky and should be
# improved in the future.
$(ABICHECK_DIR)/mlkem/src/native/aarch64/%.S.o: CFLAGS += -DMLK_CONFIG_MULTILEVEL_WITH_SHARED
$(ABICHECK_DIR)/mlkem/src/native/aarch64/%.S.o: CFLAGS += -UMLK_CONFIG_USE_NATIVE_BACKEND_ARITH
$(ABICHECK_DIR)/mlkem/src/native/aarch64/%.S.o: CFLAGS += -DMLK_ARITH_BACKEND_AARCH64
$(ABICHECK_DIR)/mlkem/src/fips202/native/aarch64/%.S.o: CFLAGS += -UMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
$(ABICHECK_DIR)/mlkem/src/fips202/native/aarch64/%.S.o: CFLAGS += -DMLK_FIPS202_AARCH64_NEED_X1_SCALAR
$(ABICHECK_DIR)/mlkem/src/fips202/native/aarch64/%.S.o: CFLAGS += -DMLK_FIPS202_AARCH64_NEED_X1_SCALAR
$(ABICHECK_DIR)/mlkem/src/fips202/native/aarch64/%.S.o: CFLAGS += -DMLK_FIPS202_AARCH64_NEED_X1_V84A
$(ABICHECK_DIR)/mlkem/src/fips202/native/aarch64/%.S.o: CFLAGS += -DMLK_FIPS202_AARCH64_NEED_X2_V84A
$(ABICHECK_DIR)/mlkem/src/fips202/native/aarch64/%.S.o: CFLAGS += -DMLK_FIPS202_AARCH64_NEED_X4_V8A_SCALAR_HYBRID
$(ABICHECK_DIR)/mlkem/src/fips202/native/aarch64/%.S.o: CFLAGS += -DMLK_FIPS202_AARCH64_NEED_X4_V8A_V84A_SCALAR_HYBRID
endif

# ABI checker binary
$(ABICHECK_DIR)/bin/abicheck: $(ABICHECK_OBJS)
