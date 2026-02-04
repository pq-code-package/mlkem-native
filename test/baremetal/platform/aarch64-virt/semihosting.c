/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * AArch64 semihosting stubs and minimal C library for bare-metal
 * execution under QEMU without newlib.
 *
 * Provides: semihosting I/O, printf/fprintf, memset/memcpy/memmove/memcmp,
 * strlen, exit, and other stubs needed by the test code.
 */

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>

/* AArch64 semihosting call numbers */
#define SYS_WRITEC 0x03
#define SYS_WRITE0 0x04
#define SYS_GET_CMDLINE 0x15
#define SYS_EXIT_EXTENDED 0x20

/* ADP_Stopped_ApplicationExit */
#define ADP_STOPPED_APPLICATION_EXIT 0x20026ULL

/*
 * Issue an AArch64 semihosting call.
 *   op  -- semihosting operation number (in w0)
 *   arg -- pointer to parameter block (in x1)
 * Returns the result in x0.
 */
static inline long semihosting_call(unsigned op, void *arg)
{
  register unsigned r0 __asm__("x0") = op;
  register void *r1 __asm__("x1") = arg;
  __asm__ volatile("hlt #0xf000" : "+r"(r0) : "r"(r1) : "memory");
  return (long)r0;
}

/* ------------------------------------------------------------------ */
/* Semihosting I/O                                                     */
/* ------------------------------------------------------------------ */

static void sh_putc(char c) { semihosting_call(SYS_WRITEC, &c); }

int _write(int fd, const char *buf, int len)
{
  (void)fd;
  for (int i = 0; i < len; i++)
  {
    sh_putc(buf[i]);
  }
  return len;
}

void _exit(int status)
{
  uint64_t block[2] = {ADP_STOPPED_APPLICATION_EXIT, (uint64_t)status};
  semihosting_call(SYS_EXIT_EXTENDED, block);
  for (;;)
    ;
}

void exit(int status) { _exit(status); }

void abort(void) { _exit(1); }

/* ------------------------------------------------------------------ */
/* Memory routines                                                     */
/* ------------------------------------------------------------------ */

void *memset(void *s, int c, size_t n)
{
  unsigned char *p = s;
  while (n--)
  {
    *p++ = (unsigned char)c;
  }
  return s;
}

void *memcpy(void *dest, const void *src, size_t n)
{
  unsigned char *d = dest;
  const unsigned char *s = src;
  while (n--)
  {
    *d++ = *s++;
  }
  return dest;
}

void *memmove(void *dest, const void *src, size_t n)
{
  unsigned char *d = dest;
  const unsigned char *s = src;
  if (d < s)
  {
    while (n--)
    {
      *d++ = *s++;
    }
  }
  else
  {
    d += n;
    s += n;
    while (n--)
    {
      *--d = *--s;
    }
  }
  return dest;
}

int memcmp(const void *s1, const void *s2, size_t n)
{
  const unsigned char *a = s1;
  const unsigned char *b = s2;
  for (size_t i = 0; i < n; i++)
  {
    if (a[i] != b[i])
    {
      return a[i] - b[i];
    }
  }
  return 0;
}

/* ------------------------------------------------------------------ */
/* String routines                                                     */
/* ------------------------------------------------------------------ */

size_t strlen(const char *s)
{
  const char *p = s;
  while (*p)
  {
    p++;
  }
  return (size_t)(p - s);
}

int strcmp(const char *s1, const char *s2)
{
  while (*s1 && *s1 == *s2)
  {
    s1++;
    s2++;
  }
  return *(const unsigned char *)s1 - *(const unsigned char *)s2;
}

char *strcpy(char *dest, const char *src)
{
  char *d = dest;
  while ((*d++ = *src++))
    ;
  return dest;
}

/* ------------------------------------------------------------------ */
/* Minimal printf/fprintf                                              */
/* ------------------------------------------------------------------ */

static void sh_puts(const char *s)
{
  while (*s)
  {
    sh_putc(*s++);
  }
}

static void sh_put_unsigned(unsigned long long v, int base, int width, char pad,
                            int is_upper)
{
  char buf[20];
  int i = 0;
  const char *digits = is_upper ? "0123456789ABCDEF" : "0123456789abcdef";

  if (v == 0)
  {
    buf[i++] = '0';
  }
  else
  {
    while (v)
    {
      buf[i++] = digits[v % (unsigned)base];
      v /= (unsigned)base;
    }
  }
  for (int j = i; j < width; j++)
  {
    sh_putc(pad);
  }
  while (i--)
  {
    sh_putc(buf[i]);
  }
}

static int sh_vprintf(const char *fmt, va_list ap)
{
  int count = 0;
  for (; *fmt; fmt++)
  {
    if (*fmt != '%')
    {
      sh_putc(*fmt);
      count++;
      continue;
    }
    fmt++;

    /* Parse optional width and zero-pad */
    char pad = ' ';
    int width = 0;
    if (*fmt == '0')
    {
      pad = '0';
      fmt++;
    }
    while (*fmt >= '0' && *fmt <= '9')
    {
      width = width * 10 + (*fmt++ - '0');
    }

    /* Parse length modifier */
    int is_long = 0;
    int is_size = 0;
    if (*fmt == 'l')
    {
      is_long = 1;
      fmt++;
      if (*fmt == 'l')
      {
        fmt++;
      }
    }
    else if (*fmt == 'z')
    {
      is_size = 1;
      fmt++;
    }

    switch (*fmt)
    {
      case 'd':
      case 'i':
      {
        long long v = is_long   ? va_arg(ap, long)
                      : is_size ? (long long)va_arg(ap, size_t)
                                : va_arg(ap, int);
        if (v < 0)
        {
          sh_putc('-');
          count++;
          v = -v;
        }
        sh_put_unsigned((unsigned long long)v, 10, width, pad, 0);
        count++;
        break;
      }
      case 'u':
      {
        unsigned long long v = is_long   ? va_arg(ap, unsigned long)
                               : is_size ? va_arg(ap, size_t)
                                         : va_arg(ap, unsigned int);
        sh_put_unsigned(v, 10, width, pad, 0);
        count++;
        break;
      }
      case 'x':
      case 'X':
      {
        unsigned long long v = is_long   ? va_arg(ap, unsigned long)
                               : is_size ? va_arg(ap, size_t)
                                         : va_arg(ap, unsigned int);
        sh_put_unsigned(v, 16, width, pad, *fmt == 'X');
        count++;
        break;
      }
      case 'p':
      {
        void *p = va_arg(ap, void *);
        sh_puts("0x");
        sh_put_unsigned((unsigned long long)(uintptr_t)p, 16, 0, '0', 0);
        count++;
        break;
      }
      case 's':
      {
        const char *s = va_arg(ap, const char *);
        sh_puts(s ? s : "(null)");
        count++;
        break;
      }
      case 'c':
      {
        char c = (char)va_arg(ap, int);
        sh_putc(c);
        count++;
        break;
      }
      case '%':
        sh_putc('%');
        count++;
        break;
      default:
        sh_putc('%');
        sh_putc(*fmt);
        count++;
        break;
    }
  }
  return count;
}

int printf(const char *fmt, ...)
{
  va_list ap;
  va_start(ap, fmt);
  int ret = sh_vprintf(fmt, ap);
  va_end(ap);
  return ret;
}

/* FILE is opaque -- we ignore the stream and print to semihosting */
int fprintf(void *stream, const char *fmt, ...)
{
  (void)stream;
  va_list ap;
  va_start(ap, fmt);
  int ret = sh_vprintf(fmt, ap);
  va_end(ap);
  return ret;
}

int puts(const char *s)
{
  sh_puts(s);
  sh_putc('\n');
  return 0;
}

/* ------------------------------------------------------------------ */
/* Exception reporting                                                 */
/* ------------------------------------------------------------------ */

void report_exception(uint64_t esr, uint64_t elr, uint64_t far);
void report_exception(uint64_t esr, uint64_t elr, uint64_t far)
{
  static const char hex[] = "0123456789abcdef";

  const char *msgs[] = {"\n*** EXCEPTION ***\nESR_EL1 = 0x", "\nELR_EL1 = 0x",
                        "\nFAR_EL1 = 0x"};
  uint64_t vals[] = {esr, elr, far};

  for (int m = 0; m < 3; m++)
  {
    sh_puts(msgs[m]);
    uint64_t v = vals[m];
    for (int i = 60; i >= 0; i -= 4)
    {
      sh_putc(hex[(v >> i) & 0xf]);
    }
  }
  sh_putc('\n');
}

/* ------------------------------------------------------------------ */
/* Newlib reentrancy stub                                              */
/* ------------------------------------------------------------------ */

/*
 * newlib's <stdio.h> defines stderr as (_REENT->_stderr), which
 * references _impure_ptr.  We are not linking newlib's libc, so we
 * provide a zeroed-out buffer.  Our own fprintf/printf never touch
 * it -- the symbol just needs to exist so the linker is happy.
 */
static char _impure_data[256] __attribute__((aligned(8)));
void *_impure_ptr = _impure_data;

/* ------------------------------------------------------------------ */
/* Command-line argument handling                                      */
/* ------------------------------------------------------------------ */

#define MAX_ARGS 32
#define CMDLINE_BUF_SIZE 65536

static char cmdline_buf[CMDLINE_BUF_SIZE];
static char *argv_ptrs[MAX_ARGS + 1];
static int g_argc;
static char **g_argv;

/*
 * Parse command line from semihosting into argc/argv.
 * QEMU passes arguments via -semihosting-config arg=...
 */
static void parse_cmdline(void)
{
  struct
  {
    char *buf;
    size_t len;
  } cmdline_block = {cmdline_buf, CMDLINE_BUF_SIZE};

  long ret = semihosting_call(SYS_GET_CMDLINE, &cmdline_block);
  if (ret != 0)
  {
    /* No command line available, provide defaults */
    g_argc = 1;
    argv_ptrs[0] = "program";
    argv_ptrs[1] = NULL;
    g_argv = argv_ptrs;
    return;
  }

  /* Parse the command line buffer into argv */
  g_argc = 0;
  char *p = cmdline_buf;
  int in_arg = 0;

  while (*p && g_argc < MAX_ARGS)
  {
    if (*p == ' ' || *p == '\t')
    {
      if (in_arg)
      {
        *p = '\0';
        in_arg = 0;
      }
    }
    else
    {
      if (!in_arg)
      {
        argv_ptrs[g_argc++] = p;
        in_arg = 1;
      }
    }
    p++;
  }
  argv_ptrs[g_argc] = NULL;
  g_argv = argv_ptrs;
}

/* Declare the real main from the test program */
int main(int argc, char **argv);

/* Entry point called from startup.S */
void _start_c(void)
{
  parse_cmdline();
  int ret = main(g_argc, g_argv);
  exit(ret);
}
