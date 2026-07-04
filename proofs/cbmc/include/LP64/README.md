[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# C Header files for CBMC proof, LP64 data model

These header files declare typedef's and constants to give
CBMC the correct data-model for the "LP64" data model,
which is that used on "64-bit UNIX-like" systems, including
Linux and macOS using both AArch64 and x86_64 processors.

"LP64" stands for "Long and Pointer are 64-bit", so
the predefined types in this model are as follows:

## Predefined integer types ##

|type|comment|MIN|MAX|
|----|-------|---|---|
|signed char|8 bits, signed, 2's complement|-128|127|
|unsigned char|8 bits, unsigned|0|255|
|short|16 bits, signed, 2's complement|-32_768|32_767|
|unsigned short|16 bits, unsigned|0|65535|
|int|32 bits, signed, 2's complement|-2_147_483_648|2_147_483_647|
|unsigned int|32 bits, unsigned|0|4_294_967_295|
|long|64 bits, signed, 2'complement|-2**63|2**63-1|
|unsigned long|64 bits, unsigned|0|2**64-1|

## Derived fixed-width types ##

These headers therefore declare fixed-width integer types
as follow (in stdint.h)

|type|base type|
|----|---------|
|int8_t|signed char|
|uint8_t|unsigned char|
|int16_t|short|
|uint16_t|unsigned short|
|int32_t|int|
|uint32_t|unsigned int|
|int64_t|long|
|uint64_t|unsigned long|

"Pointers" are 64-bit unsigned in LP64, and size_t is 64-bit
so, in stddef.h, we declare

`typedef unsigned long size_t;`

## Macros

The macro `SIZE_MAX` is required to declare preconditions that limit
buffer sizes, so

```
/* size_t is 64-bit unsigned (see stddef.h), so SIZE_MAX is 2**64-1 */
#define SIZE_MAX (18446744073709551615UL)
```

## Functions

These header files only declare functions that are required by mlkem-native and no more.

`stdlib.h` declares

```
void *malloc(size_t size);

void free(void *ptr);
```

while `string.h` declares

```
void *memset(void *dest, int ch, size_t count);

void *memcpy(void *dest, const void *src, size_t count);
```

These declarations reflect those specified in ISO C standard
(aka C90, C99 and beyond), and offer CBMC a consistent view
of these functions regardless of the platform on which
analysis is being run.
