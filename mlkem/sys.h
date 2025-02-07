/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLK_SYS_H
#define MLK_SYS_H

/* Check if we're running on an AArch64 little endian system. _M_ARM64 is set by
 * MSVC. */
#if defined(__AARCH64EL__) || defined(_M_ARM64)
#define MLK_SYS_AARCH64
#endif

/* Check if we're running on an AArch64 big endian system. */
#if defined(__AARCH64EB__)
#define MLK_SYS_AARCH64_EB
#endif

#if defined(__x86_64__)
#define MLK_SYS_X86_64
#if defined(__AVX2__)
#define MLK_SYS_X86_64_AVX2
#endif
#endif /* __x86_64__ */

/* Try to find endianness, if not forced through CFLAGS already */
#if !defined(MLK_SYS_LITTLE_ENDIAN) && !defined(MLK_SYS_BIG_ENDIAN)
#if defined(__BYTE_ORDER__)
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define MLK_SYS_LITTLE_ENDIAN
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define MLK_SYS_BIG_ENDIAN
#else /* __BYTE_ORER__ */
#error "__BYTE_ORDER__ defined, but don't recognize value."
#endif /* __BYTE_ORER__ */
#endif /* !defined(__BYTE_ORER__) */
#endif /* defined(MLK_SYS_LITTLE_ENDIAN) || defined(MLK_SYS_BIG_ENDIAN) */

/* If MLK_FORCE_AARCH64 is set, assert that we're indeed on an AArch64 system.
 */
#if defined(MLK_FORCE_AARCH64) && !defined(MLK_SYS_AARCH64)
#error "MLK_FORCE_AARCH64 is set, but we don't seem to be on an AArch64 system."
#endif

/* If MLK_FORCE_AARCH64_EB is set, assert that we're indeed on a big endian
 * AArch64 system. */
#if defined(MLK_FORCE_AARCH64_EB) && !defined(MLK_SYS_AARCH64_EB)
#error \
    "MLK_FORCE_AARCH64_EB is set, but we don't seem to be on an AArch64 system."
#endif

/* If MLK_FORCE_X86_64 is set, assert that we're indeed on an X86_64 system. */
#if defined(MLK_FORCE_X86_64) && !defined(MLK_SYS_X86_64)
#error "MLK_FORCE_X86_64 is set, but we don't seem to be on an X86_64 system."
#endif

/*
 * C90 does not have the inline compiler directive yet.
 * We don't use it in C90 builds.
 * However, in that case the compiler warns about some inline functions in
 * header files not being used in every compilation unit that includes that
 * header. To work around it we silence that warning in that case using
 * __attribute__((unused)).
 */

/* Do not use inline for C90 builds*/
#if !defined(MLK_INLINE)
#if !defined(inline)
#if defined(_MSC_VER)
#define MLK_INLINE __inline
/* Don't combine __inline and __forceinline */
#define MLK_ALWAYS_INLINE __forceinline
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
#define MLK_INLINE inline
#define MLK_ALWAYS_INLINE MLK_INLINE __attribute__((always_inline))
#else
#define MLK_INLINE __attribute__((unused))
#define MLK_ALWAYS_INLINE MLK_INLINE
#endif

#else
#define MLK_INLINE inline
#define MLK_ALWAYS_INLINE MLK_INLINE __attribute__((always_inline))
#endif
#endif

/*
 * C90 does not have the restrict compiler directive yet.
 * We don't use it in C90 builds.
 */
#if !defined(restrict)
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
#define MLK_RESTRICT restrict
#else
#define MLK_RESTRICT
#endif

#else

#define MLK_RESTRICT restrict
#endif

#define MLK_DEFAULT_ALIGN 32
#if defined(__GNUC__)
#define MLK_ALIGN __attribute__((aligned(MLK_DEFAULT_ALIGN)))
#elif defined(_MSC_VER)
#define MLK_ALIGN __declspec(align(MLK_DEFAULT_ALIGN))
#else
#define MLK_ALIGN /* No known support for alignment constraints */
#endif

#endif /* MLK_SYS_H */
