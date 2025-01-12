# SPDX-License-Identifier: Apache-2.0

FIPS202_SRCS = $(wildcard mlkem/fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard mlkem/fips202/native/aarch64/src/*.S) $(wildcard mlkem/fips202/native/aarch64/src/*.c) $(wildcard mlkem/fips202/native/x86_64/src/*.c)
endif

$(BUILD_DIR)/libmlkem.a: $(call OBJS, $(FIPS202_SRCS))
$(BUILD_DIR)/libmlkem512.a: $(call OBJS, $(FIPS202_SRCS))
$(BUILD_DIR)/libmlkem768.a: $(call OBJS, $(FIPS202_SRCS))
$(BUILD_DIR)/libmlkem1024.a: $(call OBJS, $(FIPS202_SRCS))

SOURCES += $(wildcard mlkem/*.c) $(wildcard mlkem/debug/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/native/aarch64/src/*.[csS]) $(wildcard mlkem/native/x86_64/src/*.[csS])
	CFLAGS += -DMLKEM_USE_NATIVE
endif

ALL_TESTS = test_mlkem acvp_mlkem bench_mlkem bench_components_mlkem gen_NISTKAT gen_KAT
NON_NIST_TESTS = $(filter-out gen_NISTKAT,$(ALL_TESTS))

MLKEM512_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_DIR = $(BUILD_DIR)/mlkem1024

# build lib<scheme>.a
define BUILD_LIB
$(BUILD_DIR)/lib$(1).a: CFLAGS += -static
$(BUILD_DIR)/lib$(1).a: $(call MAKE_OBJS,$(BUILD_DIR)/$(1),$(SOURCES))

# NOTE:
# libmlkem.a does not link against libmlkem{512,768,1024}.a, but the underlying object files.
# Still, we currently need a dependency on libmlkem{512,768,1024}.a here as otherwise there is
# a hiccup with the setting of MLKEM_K (TODO: look at this more closely)
$(BUILD_DIR)/libmlkem.a: $(BUILD_DIR)/lib$(1).a $(call MAKE_OBJS,$(BUILD_DIR)/$(1),$(SOURCES))
endef

$(BUILD_DIR)/libmlkem512.a: CFLAGS += -DMLKEM_K=2
$(BUILD_DIR)/libmlkem768.a: CFLAGS += -DMLKEM_K=3
$(BUILD_DIR)/libmlkem1024.a: CFLAGS += -DMLKEM_K=4

# build libmlkem512.a libmlkem768.a libmlkem1024.a
$(foreach scheme,mlkem512 mlkem768 mlkem1024, \
	$(eval $(call BUILD_LIB,$(scheme))))

# rules for compilation for all tests: mainly linking with mlkem static link library
define ADD_SOURCE
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): LDLIBS += -L$(BUILD_DIR) -l$(1)
$(BUILD_DIR)/$(1)/bin/$(2)$(shell echo $(1) | tr -d -c 0-9): $(BUILD_DIR)/$(1)/test/$(2).c.o $(BUILD_DIR)/lib$(1).a
endef

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

$(MLKEM512_DIR)/bin/%: CFLAGS += -DMLKEM_K=2
$(MLKEM768_DIR)/bin/%: CFLAGS += -DMLKEM_K=3
$(MLKEM1024_DIR)/bin/%: CFLAGS += -DMLKEM_K=4

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
