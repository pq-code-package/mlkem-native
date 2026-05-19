#ifndef MLK_PROOF_CONFIG_H
#define MLK_PROOF_CONFIG_H

/* Proof-oriented configuration for Isabelle translation. */
/* Keep symbol names compact and stable for theorem references. */
#define MLK_CONFIG_NAMESPACE_PREFIX mlk

/* Avoid accidental native backend assumptions in translated C semantics. */
#define MLK_CONFIG_NO_ASM

/* Prevent libc string header pull-in from common.h. */
#define MLK_CONFIG_CUSTOM_MEMCPY
#define MLK_CONFIG_CUSTOM_MEMSET

/* Provide simple stand-ins used only during translation extraction. */
#if !defined(__ASSEMBLER__)
typedef unsigned long size_t;

static inline void *mlk_memcpy(void *dst, const void *src, size_t n)
{
  unsigned char *d = (unsigned char *)dst;
  const unsigned char *s = (const unsigned char *)src;
  size_t i;
  for (i = 0; i < n; i++)
  {
    d[i] = s[i];
  }
  return dst;
}

static inline void *mlk_memset(void *dst, int c, size_t n)
{
  unsigned char *d = (unsigned char *)dst;
  size_t i;
  for (i = 0; i < n; i++)
  {
    d[i] = (unsigned char)c;
  }
  return dst;
}
#endif

/* Simplify constant-time opt-blocker globals to constant 0 for proof builds.
 * This makes value barriers reduce to identity (b ^ 0 = b), which is
 * functionally correct: barriers only prevent compiler optimizations.
 * Variadic macros accept the (void) parameter in function declarations. */
#define mlk_ct_get_optblocker_u32(...) ((uint32_t)0)
#define mlk_ct_get_optblocker_i32(...) ((int32_t)0)
#define mlk_ct_get_optblocker_u8(...)  ((uint8_t)0)
#define mlk_ct_get_optblocker_u64(...) ((uint64_t)0)

/* Provide a minimal zeroization implementation for preprocessing-only builds. */
#define MLK_CONFIG_CUSTOM_ZEROIZE
#if !defined(__ASSEMBLER__)
static inline void mlk_zeroize(void *ptr, size_t len)
{
  (void)ptr;
  (void)len;
}
#endif

#endif
