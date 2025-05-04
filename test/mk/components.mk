# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

FIPS202_SRCS = $(wildcard mlkem/fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard mlkem/fips202/native/aarch64/src/*.S) $(wildcard mlkem/fips202/native/aarch64/src/*.c) $(wildcard mlkem/fips202/native/x86_64/src/*.c)
endif

SOURCES += $(wildcard mlkem/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/native/aarch64/src/*.[csS]) $(wildcard mlkem/native/x86_64/src/*.[csS])
	CFLAGS += -DMLK_CONFIG_USE_NATIVE_BACKEND_ARITH -DMLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
endif

ALL_TESTS = test_mlkem acvp_mlkem bench_mlkem bench_components_mlkem gen_NISTKAT gen_KAT
NON_NIST_TESTS = $(filter-out gen_NISTKAT,$(ALL_TESTS))

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

# nistkat tests require special RNG
$(MLKEM512_DIR)/bin/gen_NISTKAT512: CFLAGS += -Itest/nistrng
$(MLKEM512_DIR)/bin/gen_NISTKAT512: $(call MAKE_OBJS, $(MLKEM512_DIR), $(wildcard test/nistrng/*.c))
$(MLKEM768_DIR)/bin/gen_NISTKAT768: CFLAGS += -Itest/nistrng
$(MLKEM768_DIR)/bin/gen_NISTKAT768: $(call MAKE_OBJS, $(MLKEM768_DIR), $(wildcard test/nistrng/*.c))
$(MLKEM1024_DIR)/bin/gen_NISTKAT1024: CFLAGS += -Itest/nistrng
$(MLKEM1024_DIR)/bin/gen_NISTKAT1024: $(call MAKE_OBJS, $(MLKEM1024_DIR), $(wildcard test/nistrng/*.c))

# All other tests use test-only RNG
$(NON_NIST_TESTS:%=$(MLKEM512_DIR)/bin/%512): $(call MAKE_OBJS, $(MLKEM512_DIR), $(wildcard test/notrandombytes/*.c))
$(NON_NIST_TESTS:%=$(MLKEM768_DIR)/bin/%768): $(call MAKE_OBJS, $(MLKEM768_DIR), $(wildcard test/notrandombytes/*.c))
$(NON_NIST_TESTS:%=$(MLKEM1024_DIR)/bin/%1024): $(call MAKE_OBJS, $(MLKEM1024_DIR), $(wildcard test/notrandombytes/*.c))
