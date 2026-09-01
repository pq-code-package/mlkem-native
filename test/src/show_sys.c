/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <limits.h>
#include <stddef.h>
#include <stdio.h>

#include "../../mlkem/src/common.h"

#if defined(MLK_SYS_RISCV64_RVV)
#include <riscv_vector.h>
#endif

#define MLK_SHOW_STRINGIFY_IMPL(x) #x
#define MLK_SHOW_STRINGIFY(x) MLK_SHOW_STRINGIFY_IMPL(x)

#define MLK_SHOW_DEFINE(name) printf(#name ": 1\n")
#define MLK_SHOW_UNDEFINE(name) printf(#name ": 0\n")

static void mlk_show_compile_time(void)
{
#ifdef MLK_HAVE_INLINE_ASM
  MLK_SHOW_DEFINE(MLK_HAVE_INLINE_ASM);
#else
  MLK_SHOW_UNDEFINE(MLK_HAVE_INLINE_ASM);
#endif

#ifdef MLK_SYS_LITTLE_ENDIAN
  MLK_SHOW_DEFINE(MLK_SYS_LITTLE_ENDIAN);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_LITTLE_ENDIAN);
#endif

#ifdef MLK_SYS_BIG_ENDIAN
  MLK_SHOW_DEFINE(MLK_SYS_BIG_ENDIAN);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_BIG_ENDIAN);
#endif

#ifdef MLK_SYS_AARCH64
  MLK_SHOW_DEFINE(MLK_SYS_AARCH64);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_AARCH64);
#endif

#ifdef MLK_SYS_AARCH64_NEON
  MLK_SHOW_DEFINE(MLK_SYS_AARCH64_NEON);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_AARCH64_NEON);
#endif

#ifdef MLK_SYS_AARCH64_EB
  MLK_SHOW_DEFINE(MLK_SYS_AARCH64_EB);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_AARCH64_EB);
#endif

#ifdef MLK_SYS_ARMV81M_MVE
  MLK_SHOW_DEFINE(MLK_SYS_ARMV81M_MVE);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_ARMV81M_MVE);
#endif

#ifdef MLK_SYS_X86_64
  MLK_SHOW_DEFINE(MLK_SYS_X86_64);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_X86_64);
#endif

#ifdef MLK_SYS_X86_64_AVX2
  MLK_SHOW_DEFINE(MLK_SYS_X86_64_AVX2);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_X86_64_AVX2);
#endif

#ifdef MLK_SYS_PPC64LE
  MLK_SHOW_DEFINE(MLK_SYS_PPC64LE);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_PPC64LE);
#endif

#ifdef MLK_SYS_RISCV64
  MLK_SHOW_DEFINE(MLK_SYS_RISCV64);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_RISCV64);
#endif

#ifdef MLK_SYS_RISCV64_RVV
  MLK_SHOW_DEFINE(MLK_SYS_RISCV64_RVV);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_RISCV64_RVV);
#endif

#ifdef MLK_SYS_RISCV32
  MLK_SHOW_DEFINE(MLK_SYS_RISCV32);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_RISCV32);
#endif

#ifdef MLK_SYS_WINDOWS
  MLK_SHOW_DEFINE(MLK_SYS_WINDOWS);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_WINDOWS);
#endif

#ifdef MLK_SYS_LINUX
  MLK_SHOW_DEFINE(MLK_SYS_LINUX);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_LINUX);
#endif

#ifdef MLK_SYS_APPLE
  MLK_SHOW_DEFINE(MLK_SYS_APPLE);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_APPLE);
#endif

#ifdef MLK_SYS_C99
  MLK_SHOW_DEFINE(MLK_SYS_C99);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_C99);
#endif

#ifdef MLK_SYS_C11
  MLK_SHOW_DEFINE(MLK_SYS_C11);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_C11);
#endif

#ifdef MLK_SYS_C17
  MLK_SHOW_DEFINE(MLK_SYS_C17);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_C17);
#endif

#ifdef MLK_SYS_C23
  MLK_SHOW_DEFINE(MLK_SYS_C23);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_C23);
#endif

#ifdef MLK_SYS_CXX
  MLK_SHOW_DEFINE(MLK_SYS_CXX);
#else
  MLK_SHOW_UNDEFINE(MLK_SYS_CXX);
#endif

#ifdef __BMI2__
  printf("__BMI2__: 1\n");
#else
  printf("__BMI2__: 0\n");
#endif

#ifdef __ARM_FEATURE_SHA3
  printf("__ARM_FEATURE_SHA3: 1\n");
#else
  printf("__ARM_FEATURE_SHA3: 0\n");
#endif

  printf("bits-int: %u\n", (unsigned)(sizeof(int) * CHAR_BIT));
  printf("bits-sizet: %u\n", (unsigned)(sizeof(size_t) * CHAR_BIT));
  printf("bits-pointer: %u\n", (unsigned)(sizeof(void *) * CHAR_BIT));

  printf("MLK_INLINE: \"%s\"\n", MLK_SHOW_STRINGIFY(MLK_INLINE));
  printf("MLK_ALWAYS_INLINE: \"%s\"\n", MLK_SHOW_STRINGIFY(MLK_ALWAYS_INLINE));
  printf("MLK_NOINLINE: \"%s\"\n", MLK_SHOW_STRINGIFY(MLK_NOINLINE));
  printf("MLK_RESTRICT: \"%s\"\n", MLK_SHOW_STRINGIFY(MLK_RESTRICT));
  printf("MLK_ALIGN: \"%s\"\n", MLK_SHOW_STRINGIFY(MLK_ALIGN));

#ifdef MLK_SYSV_ABI_SUPPORTED
  MLK_SHOW_DEFINE(MLK_SYSV_ABI_SUPPORTED);
#else
  MLK_SHOW_UNDEFINE(MLK_SYSV_ABI_SUPPORTED);
#endif

  printf("MLK_SYSV_ABI: \"%s\"\n", MLK_SHOW_STRINGIFY(MLK_SYSV_ABI));
}

static int mlk_show_runtime_capability(mlk_sys_cap cap)
{
  switch (cap)
  {
    case MLK_SYS_CAP_X86_64_AVX2:
#if defined(MLK_SYS_X86_64_AVX2)
      return mlk_sys_check_capability(cap);
#else
      return 0;
#endif

    case MLK_SYS_CAP_AARCH64_NEON:
#if defined(MLK_SYS_AARCH64_NEON)
      return mlk_sys_check_capability(cap);
#else
      return 0;
#endif

    case MLK_SYS_CAP_AARCH64_SHA3:
#if defined(MLK_SYS_AARCH64) && defined(__ARM_FEATURE_SHA3)
      return mlk_sys_check_capability(cap);
#else
      return 0;
#endif

    case MLK_SYS_CAP_ARMV81M_MVE:
#if defined(MLK_SYS_ARMV81M_MVE)
      return mlk_sys_check_capability(cap);
#else
      return 0;
#endif
  }

  return 0;
}

static unsigned mlk_show_runtime_rvv_vlen(void)
{
#if defined(MLK_SYS_RISCV64_RVV)
  return (unsigned)(__riscv_vsetvlmax_e8m1() * CHAR_BIT);
#else
  return 0;
#endif
}

static void mlk_show_runtime_caps(void)
{
  printf("MLK_SYS_CAP_X86_64_AVX2: %d\n",
         mlk_show_runtime_capability(MLK_SYS_CAP_X86_64_AVX2));
  printf("MLK_SYS_CAP_AARCH64_NEON: %d\n",
         mlk_show_runtime_capability(MLK_SYS_CAP_AARCH64_NEON));
  printf("MLK_SYS_CAP_AARCH64_SHA3: %d\n",
         mlk_show_runtime_capability(MLK_SYS_CAP_AARCH64_SHA3));
  printf("MLK_SYS_CAP_ARMV81M_MVE: %d\n",
         mlk_show_runtime_capability(MLK_SYS_CAP_ARMV81M_MVE));
  printf("runtime-rvv-vlen: %u\n", mlk_show_runtime_rvv_vlen());
}

int main(void)
{
  mlk_show_compile_time();
  mlk_show_runtime_caps();
  return 0;
}
