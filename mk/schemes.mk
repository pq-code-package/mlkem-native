# SPDX-License-Identifier: Apache-2.0
SOURCES = $(wildcard mlkem/*.c) $(wildcard mlkem/debug/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/native/aarch64/*.[csS]) $(wildcard mlkem/native/x86_64/*.[csS])
	CPPFLAGS += -DMLKEM_USE_NATIVE
	OPT_SUFFIX=opt
else
	OPT_SUFFIX=ref
endif

CPPFLAGS += -Imlkem -Imlkem/sys -Imlkem/native -Imlkem/native/aarch64 -Imlkem/native/x86_64
ALL_TESTS = test_mlkem acvp_mlkem bench_mlkem bench_components_mlkem gen_NISTKAT gen_KAT
NON_NIST_TESTS = $(filter-out gen_NISTKAT,$(ALL_TESTS))

MLKEM512_BUILD_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_BUILD_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_BUILD_DIR = $(BUILD_DIR)/mlkem1024

$(MLKEM512_BUILD_DIR)/bin/%: CPPFLAGS += -DMLKEM_K=2
$(ALL_TESTS:%=$(MLKEM512_BUILD_DIR)/bin/%512_$(OPT_SUFFIX)):$(MLKEM512_BUILD_DIR)/bin/%512_$(OPT_SUFFIX): $(MLKEM512_BUILD_DIR)/test/%.c.o $(call MAKE_OBJS,$(MLKEM512_BUILD_DIR), $(SOURCES))


$(MLKEM768_BUILD_DIR)/bin/%: CPPFLAGS += -DMLKEM_K=3
$(ALL_TESTS:%=$(MLKEM768_BUILD_DIR)/bin/%768_$(OPT_SUFFIX)):$(MLKEM768_BUILD_DIR)/bin/%768_$(OPT_SUFFIX): $(MLKEM768_BUILD_DIR)/test/%.c.o $(call MAKE_OBJS,$(MLKEM768_BUILD_DIR), $(SOURCES))

$(MLKEM1024_BUILD_DIR)/bin/%: CPPFLAGS += -DMLKEM_K=4
$(ALL_TESTS:%=$(MLKEM1024_BUILD_DIR)/bin/%1024_$(OPT_SUFFIX)):$(MLKEM1024_BUILD_DIR)/bin/%1024_$(OPT_SUFFIX): $(MLKEM1024_BUILD_DIR)/test/%.c.o $(call MAKE_OBJS,$(MLKEM1024_BUILD_DIR), $(SOURCES))

# nistkat tests require special RNG
$(MLKEM512_BUILD_DIR)/bin/gen_NISTKAT512_$(OPT_SUFFIX): CPPFLAGS += -Itest/nistrng
$(MLKEM512_BUILD_DIR)/bin/gen_NISTKAT512_$(OPT_SUFFIX): $(call MAKE_OBJS, $(MLKEM512_BUILD_DIR), $(wildcard test/nistrng/*.c))
$(MLKEM768_BUILD_DIR)/bin/gen_NISTKAT768_$(OPT_SUFFIX): CPPFLAGS += -Itest/nistrng
$(MLKEM768_BUILD_DIR)/bin/gen_NISTKAT768_$(OPT_SUFFIX): $(call MAKE_OBJS, $(MLKEM768_BUILD_DIR), $(wildcard test/nistrng/*.c))
$(MLKEM1024_BUILD_DIR)/bin/gen_NISTKAT1024_$(OPT_SUFFIX): CPPFLAGS += -Itest/nistrng
$(MLKEM1024_BUILD_DIR)/bin/gen_NISTKAT1024_$(OPT_SUFFIX): $(call MAKE_OBJS, $(MLKEM1024_BUILD_DIR), $(wildcard test/nistrng/*.c))

# All other tests use test-only RNG
$(NON_NIST_TESTS:%=$(MLKEM512_BUILD_DIR)/bin/%512_$(OPT_SUFFIX)): $(call MAKE_OBJS, $(MLKEM512_BUILD_DIR), $(wildcard test/notrandombytes/*.c))
$(NON_NIST_TESTS:%=$(MLKEM768_BUILD_DIR)/bin/%768_$(OPT_SUFFIX)): $(call MAKE_OBJS, $(MLKEM768_BUILD_DIR), $(wildcard test/notrandombytes/*.c))
$(NON_NIST_TESTS:%=$(MLKEM1024_BUILD_DIR)/bin/%1024_$(OPT_SUFFIX)): $(call MAKE_OBJS, $(MLKEM1024_BUILD_DIR), $(wildcard test/notrandombytes/*.c))
