# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

FIPS202_SRCS = $(wildcard mlkem/src/fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard mlkem/src/fips202/native/aarch64/src/*.S) $(wildcard mlkem/src/fips202/native/aarch64/src/*.c) $(wildcard mlkem/src/fips202/native/x86_64/src/*.c)
endif

SOURCES += $(wildcard mlkem/src/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/src/native/aarch64/src/*.[csS]) $(wildcard mlkem/src/native/x86_64/src/*.[csS]) $(wildcard mlkem/src/native/riscv64/src/*.[csS])
	CFLAGS += -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
endif

ALL_TESTS = test_mlkem test_unit acvp_mlkem bench_mlkem bench_components_mlkem gen_KAT test_stack

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
MLKEM512_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM512_DIR)/unit,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM512_UNIT_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=512 -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
MLKEM768_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM768_DIR)/unit,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM768_UNIT_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=768 -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
MLKEM1024_UNIT_OBJS = $(call MAKE_OBJS,$(MLKEM1024_DIR)/unit,$(SOURCES) $(FIPS202_SRCS))
$(MLKEM1024_UNIT_OBJS): CFLAGS += -DMLK_CONFIG_PARAMETER_SET=1024 -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes




$(BUILD_DIR)/libmlkem512.a: $(MLKEM512_OBJS)
$(BUILD_DIR)/libmlkem768.a: $(MLKEM768_OBJS)
$(BUILD_DIR)/libmlkem1024.a: $(MLKEM1024_OBJS)

# Unit libraries with exposed internal functions
$(BUILD_DIR)/libmlkem512_unit.a: $(MLKEM512_UNIT_OBJS)
$(BUILD_DIR)/libmlkem768_unit.a: $(MLKEM768_UNIT_OBJS)
$(BUILD_DIR)/libmlkem1024_unit.a: $(MLKEM1024_UNIT_OBJS)

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

$(MLKEM512_DIR)/bin/test_unit512: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
$(MLKEM768_DIR)/bin/test_unit768: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes
$(MLKEM1024_DIR)/bin/test_unit1024: CFLAGS += -DMLK_STATIC_TESTABLE= -Wno-missing-prototypes

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
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): LDLIBS += -L$(BUILD_DIR) -l$(1)
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): $(BUILD_DIR)/$(1)/test/$(2).c.o $(BUILD_DIR)/lib$(1).a
endef

# Special rule for test_unit - link against unit libraries with exposed internal functions
define ADD_SOURCE_UNIT
$(BUILD_DIR)/$(1)/bin/test_unit$(shell echo $(1) | tr -d -c 0-9): LDLIBS += -L$(BUILD_DIR) -l$(1)_unit
$(BUILD_DIR)/$(1)/bin/test_unit$(shell echo $(1) | tr -d -c 0-9): $(BUILD_DIR)/$(1)/test/test_unit.c.o $(BUILD_DIR)/lib$(1)_unit.a $(call MAKE_OBJS, $(BUILD_DIR)/$(1), $(wildcard test/notrandombytes/*.c))
endef

$(foreach scheme,mlkem512 mlkem768 mlkem1024, \
	$(foreach test,$(filter-out test_unit,$(ALL_TESTS)), \
		$(eval $(call ADD_SOURCE,$(scheme),$(test))) \
	) \
)

$(foreach scheme,mlkem512 mlkem768 mlkem1024, \
	$(eval $(call ADD_SOURCE_UNIT,$(scheme))) \
)

$(ALL_TESTS:%=$(MLKEM512_DIR)/bin/%512): $(call MAKE_OBJS, $(MLKEM512_DIR), $(wildcard test/notrandombytes/*.c) $(EXTRA_SOURCES))
$(ALL_TESTS:%=$(MLKEM768_DIR)/bin/%768): $(call MAKE_OBJS, $(MLKEM768_DIR), $(wildcard test/notrandombytes/*.c) $(EXTRA_SOURCES))
$(ALL_TESTS:%=$(MLKEM1024_DIR)/bin/%1024): $(call MAKE_OBJS, $(MLKEM1024_DIR), $(wildcard test/notrandombytes/*.c) $(EXTRA_SOURCES))

# Apply EXTRA_CFLAGS to EXTRA_SOURCES object files
ifneq ($(EXTRA_SOURCES),)
$(call MAKE_OBJS, $(MLKEM512_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
$(call MAKE_OBJS, $(MLKEM768_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
$(call MAKE_OBJS, $(MLKEM1024_DIR), $(EXTRA_SOURCES)): CFLAGS += $(EXTRA_SOURCES_CFLAGS)
endif
