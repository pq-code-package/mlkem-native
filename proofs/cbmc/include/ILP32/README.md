[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# C Header files for CBMC proof, ILP32 data model

These header files declare typedefs and constants to give CBMC the correct data
model for ILP32 systems, including 32-bit ARM, RV32, and many other 32-bit
microcontrollers.

"ILP32" stands for "Int, Long and Pointer are 32-bit", so the predefined types
in this model are as follows:

## Predefined integer types

|type|comment|MIN|MAX|
|----|-------|---|---|
|signed char|8 bits, signed, 2's complement|-128|127|
|unsigned char|8 bits, unsigned|0|255|
|short|16 bits, signed, 2's complement|-32_768|32_767|
|unsigned short|16 bits, unsigned|0|65535|
|int|32 bits, signed, 2's complement|-2_147_483_648|2_147_483_647|
|unsigned int|32 bits, unsigned|0|4_294_967_295|
|long|32 bits, signed, 2's complement|-2_147_483_648|2_147_483_647|
|unsigned long|32 bits, unsigned|0|4_294_967_295|
|long long|64 bits, signed, 2's complement|-2**63|2**63-1|
|unsigned long long|64 bits, unsigned|0|2**64-1|

## Derived fixed-width types

|type|base type|
|----|---------|
|int8_t|signed char|
|uint8_t|unsigned char|
|int16_t|short|
|uint16_t|unsigned short|
|int32_t|int|
|uint32_t|unsigned int|
|int64_t|long long|
|uint64_t|unsigned long long|

Pointers and `size_t` are 32-bit in ILP32, so `stddef.h` declares:

```c
typedef unsigned long size_t;
```

`stdint.h` defines `SIZE_MAX` as `2**32-1`:

```c
#define SIZE_MAX (4294967295U)
```

The function declarations in `stdlib.h` and `string.h` match those in the
LP64 headers.
