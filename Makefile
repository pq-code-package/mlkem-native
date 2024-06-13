# SPDX-License-Identifier: Apache-2.0

Q ?= @
QEMU = qemu-aarch64
CROSS_PREFIX ?=
CC := $(CROSS_PREFIX)gcc

INCLUDE_FIPS202 = -I fips202
INCLUDE_MLKEM = -I mlkem
INCLUDE_RANDOM = -I randombytes
INCLUDE_NISTRANDOM = -I test/nistrng
CFLAGS += -Wall -Wextra -Wpedantic -Wmissing-prototypes -Wredundant-decls \
  -Wshadow -Wpointer-arith -O3 -fomit-frame-pointer -pedantic \
   ${INCLUDE_MLKEM} ${INCLUDE_FIPS202}

OS := $(shell uname -s)
ifneq ($(OS),Darwin)
	CFLAGS += -static
endif

CFLAGS_RANDOMBYTES = ${CFLAGS} ${INCLUDE_RANDOM}
CFLAGS_NISTRANDOMBYTES = ${CFLAGS} ${INCLUDE_NISTRANDOM}
NISTFLAGS += -Wno-unused-result -O3 -fomit-frame-pointer
RM = /bin/rm

SOURCES = mlkem/kem.c mlkem/indcpa.c mlkem/polyvec.c mlkem/poly.c mlkem/ntt.c mlkem/cbd.c mlkem/reduce.c mlkem/verify.c
SOURCESKECCAK = $(SOURCES) fips202/keccakf1600.c fips202/fips202.c mlkem/symmetric-shake.c
SOURCESKECCAKRANDOM = $(SOURCESKECCAK) randombytes/randombytes.c
SOURCESNISTKATS = $(SOURCESKECCAK) test/nistrng/aes.c test/nistrng/rng.c

HEADERS = mlkem/params.h mlkem/kem.h mlkem/indcpa.h mlkem/polyvec.h mlkem/poly.h mlkem/ntt.h mlkem/cbd.h mlkem/reduce.h mlkem/verify.h mlkem/symmetric.h
HEADERSKECCAK = $(HEADERS) fips202/keccakf1600.h fips202/fips202.h
HEADERSKECCAKRANDOM = $(HEADERSKECCAK) randombytes/randombytes.h
HEADERNISTKATS = $(HEADERSKECCAK) test/nistrng/aes.h test/nistrng/randombytes.h

.PHONY: all mlkem kat nistkat clean

all: mlkem kat nistkat

mlkem: \
  bin/test_kyber512 \
  bin/test_kyber768 \
  bin/test_kyber1024

nistkat: \
  bin/gen_NISTKAT512 \
  bin/gen_NISTKAT768 \
  bin/gen_NISTKAT1024

kat: \
  bin/gen_KAT512 \
  bin/gen_KAT768 \
  bin/gen_KAT1024

define build-tests
bin/test_kyber$(1): test/test_kyber.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM)                   
	$(Q)echo "  CC      $$@"
	$(Q)[ -d $$(@D) ] || mkdir -p $$(@D)
	$(Q)$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=$(2) $(SOURCESKECCAKRANDOM) $$< -o $$@

bin/gen_KAT$(1): test/gen_KAT.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM)                   
	$(Q)echo "  CC      $$@"
	$(Q)[ -d $$(@D) ] || mkdir -p $$(@D)
	$(Q)$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=$(2) $(SOURCESKECCAKRANDOM) $$< -o $$@

bin/gen_NISTKAT$(1): test/gen_NISTKAT.c $(SOURCESNISTKATS) $(HEADERNISTKATS)                   
	$(Q)echo "  CC      $$@"
	$(Q)[ -d $$(@D) ] || mkdir -p $$(@D)
	$(Q)$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=$(2) $(SOURCESNISTKATS) $$< -o $$@
endef

KEM_SCHEMES=mlkem512 mlkem768 mlkem1024
KEM_PARAMS=2 3 4

iter=$(let scheme k rest,$(1), \
	$(eval $(call build-tests,$(scheme:mlkem%=%),$(k))) \
	$(if $(rest),$(call iter,$(rest)) ))

$(call iter,$(subst -, ,$(join $(addsuffix -,$(KEM_SCHEMES)),$(KEM_PARAMS))))

# emulate ARM64 binary on x86_64 machine
emulate:
	$(Q)$(MAKE) --quiet CROSS_PREFIX=aarch64-none-linux-gnu- $(TARGET)
	$(Q)$(QEMU) $(TARGET)

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf bin
