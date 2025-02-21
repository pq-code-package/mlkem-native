# SPDX-License-Identifier: Apache-2.0

$(BUILD_DIR)/mlkem512/bin/%: $(CONFIG)
	$(Q)echo "  LD      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(LD) $(CFLAGS) -o $@ $(filter %.o,$^) $(LDLIBS)

$(BUILD_DIR)/mlkem768/bin/%: $(CONFIG)
	$(Q)echo "  LD      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(LD) $(CFLAGS) -o $@ $(filter %.o,$^) $(LDLIBS)

$(BUILD_DIR)/mlkem1024/bin/%: $(CONFIG)
	$(Q)echo "  LD      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(LD) $(CFLAGS) -o $@ $(filter %.o,$^) $(LDLIBS)

$(BUILD_DIR)/%.a: $(CONFIG)
	$(Q)echo "  AR      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)rm -f $@
	$(Q)$(CC_AR) rcs $@ $(filter %.o,$^)
        # $AR doesn't care about duplicated symbols, one can only find it out
        # via actually linking. The easiest one to do this that one can think
        # of is to create a dummy C file with empty main function on the fly,
        # pipe it to $CC and link with the built library
	$(eval _LIB := $(subst $(BUILD_DIR)/lib,,$(@:%.a=%)))
	$(eval _CFLAGS := $(subst -static,,$(CFLAGS)))

ifeq ($(findstring Darwin,$(HOST_PLATFORM))$(CROSS_PREFIX),Darwin) # if is on native macOS
	$(Q)echo "int main(void) {return 0;}" \
		| $(CC) -x c - -L$(BUILD_DIR) $(_CFLAGS) \
		 -all_load -Wl,-undefined,dynamic_lookup -l$(_LIB) \
		 -Imlkem $(wildcard test/notrandombytes/*.c) -o $(@:%.a=%_tmp.a.out)
	$(Q)rm -f $(@:%.a=%_tmp.a.out)
else                                           # if not on macOS or cross compiling on macOS
	$(Q)echo "int main(void) {return 0;}" \
		| $(CC) -x c - -L$(BUILD_DIR) $(_CFLAGS) \
		-Wl,--whole-archive,--unresolved-symbols=ignore-in-object-files -l$(_LIB) \
		-Wl,--no-whole-archive \
		-Imlkem $(wildcard test/notrandombytes/*.c) -o $(@:%.a=%_tmp.a.out)
	$(Q)rm -f $(@:%.a=%_tmp.a.out)
endif
	$(Q)echo "  AR         Checked for duplicated symbols"

$(BUILD_DIR)/mlkem512/%.c.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem512/%.S.o: %.S $(CONFIG)
	$(Q)echo "  AS      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem768/%.c.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem768/%.S.o: %.S $(CONFIG)
	$(Q)echo "  AS      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem1024/%.c.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem1024/%.S.o: %.S $(CONFIG)
	$(Q)echo "  AS      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<
