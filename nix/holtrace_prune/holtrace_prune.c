/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * holtrace-prune: keep only the lines of a HOLTrace trace that the named
 * theorems need. A drop-in replacement for HOLTrace's Python
 * holtrace-prune, with the same arguments and output.
 *
 * Usage: holtrace-prune [NAME...] <trace >pruned
 *
 * Without names, every named theorem is kept. The input must be a
 * regular file, since it is read three times:
 *
 * 1. Forward: count the types, terms, theorems, inferences and type
 *    definitions, record which inference defines each constant and type
 *    operator, and collect the theorem names.
 * 2. Backward: mark what the selected theorems need. Every reference in
 *    a trace is to an earlier line, so a single sweep from the end
 *    marks everything, with one bit per record.
 * 3. Forward: print the marked lines in their original order, with
 *    references renumbered by rank among the marked records and
 *    encoded as the Python pruner encodes them.
 *
 * The pruner is outside HOLTrace's trusted base: replay and comparison
 * with the accepted files check its output.
 */

#define _GNU_SOURCE
#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define IN_CHUNK ((size_t)64 << 20)
#define OUT_CHUNK ((size_t)64 << 20)

static void die(const char *fmt, ...)
{
  va_list ap;
  fputs("holtrace-prune: ", stderr);
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void *xmalloc(size_t n)
{
  void *p = malloc(n ? n : 1);
  if (!p)
  {
    die("out of memory (%zu bytes)", n);
  }
  return p;
}

static void *xcalloc(size_t n, size_t s)
{
  void *p = calloc(n ? n : 1, s ? s : 1);
  if (!p)
  {
    die("out of memory (%zu x %zu bytes)", n, s);
  }
  return p;
}

static void *xrealloc(void *p, size_t n)
{
  p = realloc(p, n ? n : 1);
  if (!p)
  {
    die("out of memory (%zu bytes)", n);
  }
  return p;
}

/* ------------------------------------------------------------------ */
/* Numbers                                                             */
/* ------------------------------------------------------------------ */

/* The Python pruner's symbol2int: '!' is 1 back, ..., ')' is 10 back. */
static int symbol_value(unsigned char c)
{
  switch (c)
  {
    case '!':
      return 1;
    case '@':
      return 2;
    case '#':
      return 3;
    case '$':
      return 4;
    case '%':
      return 5;
    case '^':
      return 6;
    case '&':
      return 7;
    case '*':
      return 8;
    case '(':
      return 9;
    case ')':
      return 10;
    default:
      return 0;
  }
}

static const char symbol_char[11] = {0,   '!', '@', '#', '$', '%',
                                     '^', '&', '*', '(', ')'};

/* intencode_bytes: base 32 with digits 0-9 and A-V. */
static int is_enc(unsigned char c)
{
  return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'V');
}

/* parse_nonneg: digits, then an optional space that is consumed. */
static int64_t parse_nonneg(const unsigned char **pp, const unsigned char *end)
{
  const unsigned char *p = *pp;
  uint64_t r = 0;
  while (p < end)
  {
    unsigned c = *p;
    unsigned d;
    if (c == ' ')
    {
      p++;
      break;
    }
    if (c >= '0' && c <= '9')
    {
      d = c - '0';
    }
    else if (c >= 'A' && c <= 'V')
    {
      d = c - 'A' + 10;
    }
    else
    {
      break;
    }
    if (r > (((uint64_t)INT64_MAX) - d) / 32)
    {
      die("number too large");
    }
    r = 32 * r + d;
    p++;
  }
  *pp = p;
  return (int64_t)r;
}

/*
 * parse_num(s, id, toobig): parse_core, then the Python pruner's two
 * assertions: something was consumed, and n < toobig unless toobig < 0.
 * References (toobig >= 0) must also not be negative; Python would
 * accept them and index lists from the end.
 */
static int64_t parse_num(const unsigned char **pp, const unsigned char *end,
                         int64_t id, int64_t toobig)
{
  const unsigned char *start = *pp;
  const unsigned char *p = start;
  int64_t n;
  if (p == end)
  {
    die("missing number");
  }
  if (symbol_value(*p))
  {
    n = id - symbol_value(*p);
    p++;
  }
  else if (*p == '-')
  {
    p++;
    n = id - parse_nonneg(&p, end);
  }
  else
  {
    n = parse_nonneg(&p, end);
  }
  if (p == start)
  {
    die("missing number");
  }
  if (toobig >= 0 && (n >= toobig || n < 0))
  {
    die("reference %lld out of range %lld", (long long)n, (long long)toobig);
  }
  *pp = p;
  return n;
}

/* ------------------------------------------------------------------ */
/* Name tables (const2inf, app2inf)                                    */
/* ------------------------------------------------------------------ */

/* Keys are copied; values are inference numbers or -1 for None. */
typedef struct
{
  char *key;
  size_t len;
  int64_t val;
} entry;

typedef struct
{
  entry *e;
  size_t cap;
  size_t n;
} table;

static uint64_t hash_bytes(const unsigned char *s, size_t n)
{
  uint64_t h = 1469598103934665603ull;
  size_t i;
  for (i = 0; i < n; i++)
  {
    h ^= s[i];
    h *= 1099511628211ull;
  }
  return h ^ (h >> 29);
}

static entry *table_find(table *t, const unsigned char *k, size_t n)
{
  size_t i = hash_bytes(k, n) & (t->cap - 1);
  while (t->e[i].key)
  {
    if (t->e[i].len == n && memcmp(t->e[i].key, k, n) == 0)
    {
      return &t->e[i];
    }
    i = (i + 1) & (t->cap - 1);
  }
  return &t->e[i];
}

static void table_init(table *t)
{
  t->cap = 1024;
  t->n = 0;
  t->e = xcalloc(t->cap, sizeof(entry));
}

static void table_put(table *t, const unsigned char *k, size_t n, int64_t v)
{
  entry *e;
  if (2 * (t->n + 1) > t->cap)
  {
    entry *old = t->e;
    size_t oldcap = t->cap, i;
    t->cap *= 2;
    t->e = xcalloc(t->cap, sizeof(entry));
    for (i = 0; i < oldcap; i++)
    {
      if (old[i].key)
      {
        *table_find(t, (unsigned char *)old[i].key, old[i].len) = old[i];
      }
    }
    free(old);
  }
  e = table_find(t, k, n);
  if (!e->key)
  {
    e->key = xmalloc(n + 1);
    memcpy(e->key, k, n);
    e->len = n;
    t->n++;
  }
  e->val = v;
}

/* Returns 1 and sets *v if present. */
static int table_get(table *t, const unsigned char *k, size_t n, int64_t *v)
{
  entry *e = table_find(t, k, n);
  if (!e->key)
  {
    return 0;
  }
  *v = e->val;
  return 1;
}

/* ------------------------------------------------------------------ */
/* Bit sets with rank                                                  */
/* ------------------------------------------------------------------ */

typedef struct
{
  uint64_t *w;
  uint64_t *rank; /* number of set bits before word i */
  int64_t n;
} bits;

static void bits_init(bits *b, int64_t n)
{
  b->n = n;
  b->w = xcalloc((size_t)(n / 64 + 1), sizeof(uint64_t));
  b->rank = NULL;
}

static inline void bits_set(bits *b, int64_t i)
{
  b->w[i >> 6] |= (uint64_t)1 << (i & 63);
}

static inline int bits_get(const bits *b, int64_t i)
{
  return (int)((b->w[i >> 6] >> (i & 63)) & 1);
}

static void bits_build_rank(bits *b)
{
  size_t nw = (size_t)(b->n / 64 + 1), i;
  uint64_t r = 0;
  b->rank = xmalloc(nw * sizeof(uint64_t));
  for (i = 0; i < nw; i++)
  {
    b->rank[i] = r;
    r += (uint64_t)__builtin_popcountll(b->w[i]);
  }
}

/* Number of set bits before i: the new number of record i. */
static inline int64_t bits_rank(const bits *b, int64_t i)
{
  uint64_t mask = ((uint64_t)1 << (i & 63)) - 1;
  return (int64_t)(b->rank[i >> 6] +
                   (uint64_t)__builtin_popcountll(b->w[i >> 6] & mask));
}

/* ------------------------------------------------------------------ */
/* Input                                                               */
/* ------------------------------------------------------------------ */

static int in_fd;
static off_t in_size;

static void open_input(void)
{
  struct stat st;
  if (fstat(0, &st) != 0 || !S_ISREG(st.st_mode))
  {
    die("the input must be a regular file");
  }
  in_fd = 0;
  in_size = st.st_size;
}

static void read_at(char *buf, size_t n, off_t off)
{
  while (n > 0)
  {
    ssize_t r = pread(in_fd, buf, n, off);
    if (r <= 0)
    {
      die("cannot read the input: %s", r < 0 ? strerror(errno) : "short read");
    }
    buf += r;
    n -= (size_t)r;
    off += r;
  }
}

/* The last newline in buf[0, n), or NULL. */
static char *last_newline(char *buf, size_t n)
{
#ifdef __GLIBC__
  return memrchr(buf, '\n', n);
#else
  while (n > 0)
  {
    if (buf[--n] == '\n')
    {
      return buf + n;
    }
  }
  return NULL;
#endif /* !__GLIBC__ */
}

/* Calls f(line, len, ctx) for each line without its newline, first to last. */
typedef void (*line_fn)(const unsigned char *, size_t, void *);

static void each_line_forward(line_fn f, void *ctx)
{
  size_t cap = IN_CHUNK, have = 0;
  char *buf = xmalloc(cap);
  off_t off = 0;
  while (off < in_size || have > 0)
  {
    size_t want = cap - have, i = 0;
    if ((off_t)want > in_size - off)
    {
      want = (size_t)(in_size - off);
    }
    read_at(buf + have, want, off);
    off += (off_t)want;
    have += want;
    for (;;)
    {
      char *nl = memchr(buf + i, '\n', have - i);
      if (!nl)
      {
        break;
      }
      f((unsigned char *)buf + i, (size_t)(nl - (buf + i)), ctx);
      i = (size_t)(nl - buf) + 1;
    }
    if (off == in_size)
    {
      if (i != have)
      {
        die("final newline is required");
      }
      break;
    }
    memmove(buf, buf + i, have - i);
    have -= i;
    if (have == cap)
    {
      cap *= 2;
      buf = xrealloc(buf, cap);
    }
  }
  free(buf);
}

/* As each_line_forward, but last to first, and without the first line. */
static void each_line_backward(line_fn f, void *ctx)
{
  size_t cap = IN_CHUNK + 4096, ccap = 4096, clen = 0;
  char *buf = xmalloc(cap), *carry = xmalloc(ccap);
  off_t e = in_size, s;
  while (e > 0)
  {
    size_t n, total, hi;
    s = e > (off_t)IN_CHUNK ? e - (off_t)IN_CHUNK : 0;
    n = (size_t)(e - s);
    if (n + clen > cap)
    {
      cap = n + clen;
      buf = xrealloc(buf, cap);
    }
    read_at(buf, n, s);
    memcpy(buf + n, carry, clen);
    total = n + clen;
    /* buf[0, total) is the input from s on; it ends with a newline. */
    hi = total;
    for (;;)
    {
      char *q = last_newline(buf, hi - 1);
      if (!q)
      {
        break;
      }
      f((unsigned char *)q + 1, (size_t)(buf + hi - 1 - (q + 1)), ctx);
      hi = (size_t)(q - buf) + 1;
    }
    if (s == 0)
    {
      break; /* buf[0, hi) is the first line */
    }
    if (hi > ccap)
    {
      ccap = hi;
      carry = xrealloc(carry, ccap);
    }
    memcpy(carry, buf, hi);
    clen = hi;
    e = s;
  }
  free(buf);
  free(carry);
}

/* ------------------------------------------------------------------ */
/* State                                                               */
/* ------------------------------------------------------------------ */

typedef struct
{
  int64_t thm;
  const char *name; /* copied */
  size_t len;
  int64_t order;
} named;

static int64_t ntype, nterm, nthm, ninf, ntypedef;
static table const2inf, app2inf;
static int64_t *typedefs; /* inference number of each type definition */
static size_t typedefs_cap;
static named *names;
static size_t nnames, names_cap;
static int first_line_seen;

/* Counters during a pass: numbers of records before the current line. */
static int64_t cty, ctm, cth, cinf, ctd;

static bits want_type, want_term, want_thm, want_inf;

/* Split an 'A' line's text into prefix, abstypename, absname, repname. */
static void split_typedef(const unsigned char *s, const unsigned char *end,
                          const unsigned char *part[4], size_t plen[4])
{
  int k;
  for (k = 0; k < 4; k++)
  {
    const unsigned char *q;
    if (s > end)
    {
      die("type definition needs four ']'-separated fields");
    }
    q = memchr(s, ']', (size_t)(end - s));
    part[k] = s;
    plen[k] = (size_t)((q ? q : end) - s);
    s = q ? q + 1 : end + 1;
  }
}

/* ------------------------------------------------------------------ */
/* Pass 1: check and count                                             */
/* ------------------------------------------------------------------ */

static void pass1_line(const unsigned char *line, size_t len, void *ctx)
{
  const unsigned char *p = line + 1, *end = line + len;
  (void)ctx;
  if (len < 1)
  {
    die("blank line is prohibited");
  }
  if (!first_line_seen)
  {
    if (len != 10 || memcmp(line, "HOLTrace 1", 10) != 0)
    {
      die("first line is not HOLTrace 1");
    }
    first_line_seen = 1;
    return;
  }
  switch (line[0])
  {
    case 'a':
      ntype++;
      break;
    case 'b':
    {
      int64_t k = parse_num(&p, end, -1, -1);
      for (; k > 0; k--)
      {
        parse_num(&p, end, ntype, ntype);
      }
      ntype++;
      break;
    }
    case 'c':
    case 'd':
      parse_num(&p, end, ntype, ntype);
      nterm++;
      break;
    case 'e':
    case 'f':
      parse_num(&p, end, ntype, ntype);
      parse_num(&p, end, nterm, nterm);
      parse_num(&p, end, nterm, nterm);
      if (p != end)
      {
        die("trailing text");
      }
      nterm++;
      break;
    case 't':
      if (ninf == 0)
      {
        die("must have inference before first t line");
      }
      while (p < end)
      {
        parse_num(&p, end, nterm, nterm);
      }
      nthm++;
      break;
    case '/':
    {
      int64_t t = parse_num(&p, end, nthm, nthm);
      char *copy = xmalloc((size_t)(end - p) + 1);
      memcpy(copy, p, (size_t)(end - p));
      if (nnames == names_cap)
      {
        names_cap = names_cap ? 2 * names_cap : 1024;
        names = xrealloc(names, names_cap * sizeof(named));
      }
      names[nnames].thm = t;
      names[nnames].name = copy;
      names[nnames].len = (size_t)(end - p);
      names[nnames].order = (int64_t)nnames;
      nnames++;
      break;
    }
    case ',':
    case ';':
      break;
    case 'X':
    case 'B':
    case 'R':
    case 'U':
      parse_num(&p, end, nterm, nterm);
      if (p != end)
      {
        die("trailing text");
      }
      ninf++;
      break;
    case 'P':
    case 'V':
    case 'Z':
    case 'E':
      parse_num(&p, end, nthm, nthm);
      parse_num(&p, end, nthm, nthm);
      if (p != end)
      {
        die("trailing text");
      }
      ninf++;
      break;
    case 'F':
      parse_num(&p, end, nterm, nterm);
      parse_num(&p, end, nthm, nthm);
      if (p != end)
      {
        die("trailing text");
      }
      ninf++;
      break;
    case 'S':
      parse_num(&p, end, nthm, nthm);
      while (p < end)
      {
        parse_num(&p, end, nterm, nterm);
      }
      ninf++;
      break;
    case 'T':
      parse_num(&p, end, nthm, nthm);
      while (p < end)
      {
        parse_num(&p, end, ntype, ntype);
      }
      ninf++;
      break;
    case 'C':
    {
      int64_t v;
      parse_num(&p, end, nterm, nterm);
      if (table_get(&const2inf, p, (size_t)(end - p), &v))
      {
        die("const2inf collision");
      }
      table_put(&const2inf, p, (size_t)(end - p), ninf);
      ninf++;
      break;
    }
    case 'A':
    {
      const unsigned char *part[4];
      size_t plen[4];
      int64_t v;
      parse_num(&p, end, ntype, ntype);
      parse_num(&p, end, nterm, nterm);
      parse_num(&p, end, nthm, nthm);
      split_typedef(p, end, part, plen);
      if (plen[0] == 0)
      {
        if (table_get(&const2inf, part[2], plen[2], &v) ||
            table_get(&const2inf, part[3], plen[3], &v))
        {
          die("type definition redefines a constant");
        }
        table_put(&const2inf, part[2], plen[2], ninf);
        table_put(&const2inf, part[3], plen[3], ninf);
        if (table_get(&app2inf, part[1], plen[1], &v))
        {
          die("type definition redefines a type operator");
        }
        table_put(&app2inf, part[1], plen[1], ninf);
      }
      if ((size_t)ntypedef == typedefs_cap)
      {
        typedefs_cap = typedefs_cap ? 2 * typedefs_cap : 1024;
        typedefs = xrealloc(typedefs, typedefs_cap * sizeof(int64_t));
      }
      typedefs[ntypedef++] = ninf;
      ninf++;
      break;
    }
    case 'D':
      parse_num(&p, end, ntypedef, ntypedef);
      ninf++;
      break;
    default:
      die("unrecognized tag %c", line[0]);
  }
}

/* ------------------------------------------------------------------ */
/* Pass 2: mark, last line first                                       */
/* ------------------------------------------------------------------ */

static inline void mark_inf_name(table *t, const unsigned char *k, size_t n)
{
  int64_t v;
  if (!table_get(t, k, n, &v))
  {
    die("unknown constant or type operator");
  }
  if (v >= 0)
  {
    bits_set(&want_inf, v);
  }
}

static void pass2_line(const unsigned char *line, size_t len, void *ctx)
{
  const unsigned char *p = line + 1, *end = line + len;
  unsigned char tag = line[0];
  (void)ctx;
  switch (tag)
  {
    case 'a':
      --cty;
      return;
    case 'b':
    {
      int64_t k;
      if (!bits_get(&want_type, --cty))
      {
        return;
      }
      k = parse_num(&p, end, -1, -1);
      for (; k > 0; k--)
      {
        bits_set(&want_type, parse_num(&p, end, cty, cty));
      }
      mark_inf_name(&app2inf, p, (size_t)(end - p));
      return;
    }
    case 'c':
    case 'd':
      if (!bits_get(&want_term, --ctm))
      {
        return;
      }
      bits_set(&want_type, parse_num(&p, end, cty, cty));
      if (tag == 'c')
      {
        mark_inf_name(&const2inf, p, (size_t)(end - p));
      }
      return;
    case 'e':
    case 'f':
      if (!bits_get(&want_term, --ctm))
      {
        return;
      }
      bits_set(&want_type, parse_num(&p, end, cty, cty));
      bits_set(&want_term, parse_num(&p, end, ctm, ctm));
      bits_set(&want_term, parse_num(&p, end, ctm, ctm));
      return;
    case 't':
      if (!bits_get(&want_thm, --cth))
      {
        return;
      }
      while (p < end)
      {
        bits_set(&want_term, parse_num(&p, end, ctm, ctm));
      }
      bits_set(&want_inf, cinf - 1);
      return;
    case '/':
    case ',':
    case ';':
      return;
    default:
      break;
  }
  /* An inference. */
  --cinf;
  if (tag == 'A')
  {
    --ctd;
  }
  if (!bits_get(&want_inf, cinf))
  {
    return;
  }
  switch (tag)
  {
    case 'X':
    case 'B':
    case 'R':
    case 'U':
    case 'C':
      bits_set(&want_term, parse_num(&p, end, ctm, ctm));
      break;
    case 'P':
    case 'V':
    case 'Z':
    case 'E':
      bits_set(&want_thm, parse_num(&p, end, cth, cth));
      bits_set(&want_thm, parse_num(&p, end, cth, cth));
      break;
    case 'F':
      bits_set(&want_term, parse_num(&p, end, ctm, ctm));
      bits_set(&want_thm, parse_num(&p, end, cth, cth));
      break;
    case 'S':
      bits_set(&want_thm, parse_num(&p, end, cth, cth));
      while (p < end)
      {
        bits_set(&want_term, parse_num(&p, end, ctm, ctm));
      }
      break;
    case 'T':
      bits_set(&want_thm, parse_num(&p, end, cth, cth));
      while (p < end)
      {
        bits_set(&want_type, parse_num(&p, end, cty, cty));
      }
      break;
    case 'A':
      bits_set(&want_type, parse_num(&p, end, cty, cty));
      bits_set(&want_term, parse_num(&p, end, ctm, ctm));
      bits_set(&want_thm, parse_num(&p, end, cth, cth));
      break;
    case 'D':
      /* visit_typedef marks the type definition's inference. */
      bits_set(&want_inf, typedefs[parse_num(&p, end, ctd, ctd)]);
      break;
    default:
      die("internal error: tag %c", tag);
  }
}

/* ------------------------------------------------------------------ */
/* Pass 3: print                                                       */
/* ------------------------------------------------------------------ */

static char *out_buf;
static size_t out_len;
static size_t line_res; /* length of the current line after its tag */
static char line_last;  /* last byte written on the current line */

static void out_flush(void)
{
  size_t off = 0;
  while (off < out_len)
  {
    ssize_t w = write(1, out_buf + off, out_len - off);
    if (w <= 0)
    {
      die("cannot write the output: %s", w < 0 ? strerror(errno) : "short");
    }
    off += (size_t)w;
  }
  out_len = 0;
}

static inline void out_reserve(size_t n)
{
  if (out_len + n > OUT_CHUNK)
  {
    out_flush();
  }
  if (n > OUT_CHUNK)
  {
    die("line too long");
  }
}

static inline void line_start(unsigned char tag)
{
  out_reserve(1);
  out_buf[out_len++] = (char)tag;
  line_res = 0;
}

static inline void line_end(void)
{
  out_reserve(1);
  out_buf[out_len++] = '\n';
}

/* One field of log(): a space if both sides are digits (or it starts
   with a space), then the field. Empty fields are skipped. */
static inline void field(const char *s, size_t n)
{
  if (n == 0)
  {
    return;
  }
  out_reserve(n + 1);
  if ((is_enc((unsigned char)s[0]) || s[0] == ' ') && line_res > 0 &&
      is_enc((unsigned char)line_last))
  {
    out_buf[out_len++] = ' ';
    line_res++;
  }
  memcpy(out_buf + out_len, s, n);
  out_len += n;
  line_res += n;
  line_last = s[n - 1];
}

static int enc_len(uint64_t x)
{
  int n = 1;
  while (x >= 32)
  {
    x >>= 5;
    n++;
  }
  return n;
}

/* simpleencode(int) */
static void field_int(int64_t v)
{
  static const char digits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUV";
  char tmp[24];
  int i = 24;
  uint64_t x = v < 0 ? (uint64_t)(-v) : (uint64_t)v;
  do
  {
    tmp[--i] = digits[x & 31];
    x >>= 5;
  } while (x);
  if (v < 0)
  {
    tmp[--i] = '-';
  }
  field(tmp + i, (size_t)(24 - i));
}

/* compress(x, reference): a symbol for 1-10 back, else the shorter of
   the negative offset and the absolute number. */
static void field_ref(int64_t x, int64_t ref)
{
  int64_t back = ref - x, y = x - ref;
  if (back >= 1 && back <= 10)
  {
    field(&symbol_char[back], 1);
    return;
  }
  if (y < 0 && 1 + enc_len((uint64_t)(-y)) <= enc_len((uint64_t)x))
  {
    field_int(y);
    return;
  }
  field_int(x);
}

static bits want_A; /* type definitions whose inference is printed */
static int64_t nty_new, ntm_new, nth_new, ninf_new, ntd_new;
static size_t name_cursor;

static inline void ref_type(int64_t old)
{
  field_ref(bits_rank(&want_type, old), nty_new);
}
static inline void ref_term(int64_t old)
{
  field_ref(bits_rank(&want_term, old), ntm_new);
}
static inline void ref_thm(int64_t old)
{
  field_ref(bits_rank(&want_thm, old), nth_new);
}

static void pass3_line(const unsigned char *line, size_t len, void *ctx)
{
  const unsigned char *p = line + 1, *end = line + len;
  unsigned char tag = line[0];
  int *first = ctx;
  if (*first)
  {
    *first = 0;
    return;
  }
  switch (tag)
  {
    case 'a':
      if (bits_get(&want_type, cty))
      {
        line_start(tag);
        field((const char *)p, (size_t)(end - p));
        line_end();
        nty_new++;
      }
      cty++;
      return;
    case 'b':
      if (bits_get(&want_type, cty))
      {
        int64_t k = parse_num(&p, end, -1, -1), args[64], *a = args, i;
        int64_t count = k > 0 ? k : 0;
        if (count > 64)
        {
          a = xmalloc((size_t)count * sizeof(int64_t));
        }
        for (i = 0; i < count; i++)
        {
          a[i] = parse_num(&p, end, cty, cty);
        }
        line_start(tag);
        field_int(count);
        for (i = 0; i < count; i++)
        {
          ref_type(a[i]);
        }
        field((const char *)p, (size_t)(end - p));
        line_end();
        if (a != args)
        {
          free(a);
        }
        nty_new++;
      }
      cty++;
      return;
    case 'c':
    case 'd':
      if (bits_get(&want_term, ctm))
      {
        int64_t ty = parse_num(&p, end, cty, cty);
        line_start(tag);
        ref_type(ty);
        field((const char *)p, (size_t)(end - p));
        line_end();
        ntm_new++;
      }
      ctm++;
      return;
    case 'e':
    case 'f':
      if (bits_get(&want_term, ctm))
      {
        int64_t tt = parse_num(&p, end, cty, cty);
        int64_t t0 = parse_num(&p, end, ctm, ctm);
        int64_t t1 = parse_num(&p, end, ctm, ctm);
        line_start(tag);
        ref_type(tt);
        ref_term(t0);
        ref_term(t1);
        line_end();
        ntm_new++;
      }
      ctm++;
      return;
    case 't':
      while (name_cursor < nnames && names[name_cursor].thm < cth)
      {
        name_cursor++;
      }
      if (bits_get(&want_thm, cth))
      {
        line_start(tag);
        while (p < end)
        {
          ref_term(parse_num(&p, end, ctm, ctm));
        }
        line_end();
        nth_new++;
        while (name_cursor < nnames && names[name_cursor].thm == cth)
        {
          line_start('/');
          field_ref(nth_new - 1, nth_new);
          field(names[name_cursor].name, names[name_cursor].len);
          line_end();
          name_cursor++;
        }
      }
      cth++;
      return;
    case '/':
    case ',':
    case ';':
      return;
    default:
      break;
  }
  /* An inference. */
  if (bits_get(&want_inf, cinf))
  {
    line_start(tag);
    switch (tag)
    {
      case 'X':
      case 'B':
      case 'R':
      case 'U':
        ref_term(parse_num(&p, end, ctm, ctm));
        break;
      case 'P':
      case 'V':
      case 'Z':
      case 'E':
      {
        int64_t a = parse_num(&p, end, cth, cth);
        int64_t b = parse_num(&p, end, cth, cth);
        ref_thm(a);
        ref_thm(b);
        break;
      }
      case 'F':
      {
        int64_t a = parse_num(&p, end, ctm, ctm);
        int64_t b = parse_num(&p, end, cth, cth);
        ref_term(a);
        ref_thm(b);
        break;
      }
      case 'S':
        ref_thm(parse_num(&p, end, cth, cth));
        while (p < end)
        {
          ref_term(parse_num(&p, end, ctm, ctm));
        }
        break;
      case 'T':
        ref_thm(parse_num(&p, end, cth, cth));
        while (p < end)
        {
          ref_type(parse_num(&p, end, cty, cty));
        }
        break;
      case 'C':
        ref_term(parse_num(&p, end, ctm, ctm));
        field((const char *)p, (size_t)(end - p));
        break;
      case 'A':
      {
        int64_t a = parse_num(&p, end, cty, cty);
        int64_t b = parse_num(&p, end, ctm, ctm);
        int64_t c = parse_num(&p, end, cth, cth);
        ref_type(a);
        ref_term(b);
        ref_thm(c);
        field((const char *)p, (size_t)(end - p));
        break;
      }
      case 'D':
        field_ref(bits_rank(&want_A, parse_num(&p, end, ctd, ctd)), ntd_new);
        break;
      default:
        die("internal error: tag %c", tag);
    }
    line_end();
    ninf_new++;
    if (tag == 'A')
    {
      ntd_new++;
    }
  }
  cinf++;
  if (tag == 'A')
  {
    ctd++;
  }
}

/* ------------------------------------------------------------------ */

static int by_thm(const void *a, const void *b)
{
  const named *x = a, *y = b;
  if (x->thm != y->thm)
  {
    return x->thm < y->thm ? -1 : 1;
  }
  return x->order < y->order ? -1 : (x->order > y->order);
}

int main(int argc, char **argv)
{
  size_t i, j;
  int first = 1;

  open_input();
  table_init(&const2inf);
  table_init(&app2inf);
  table_put(&const2inf, (const unsigned char *)"=", 1, -1);
  table_put(&const2inf, (const unsigned char *)"@", 1, -1);
  table_put(&app2inf, (const unsigned char *)"bool", 4, -1);
  table_put(&app2inf, (const unsigned char *)"fun", 3, -1);
  table_put(&app2inf, (const unsigned char *)"ind", 3, -1);

  /* Pass 1 */
  if (in_size == 0)
  {
    die("empty file");
  }
  each_line_forward(pass1_line, NULL);
  if (!first_line_seen)
  {
    die("empty file");
  }

  /* Roots: every named theorem with one of the given names, or every
     named theorem if no names are given. */
  qsort(names, nnames, sizeof(named), by_thm);
  bits_init(&want_type, ntype);
  bits_init(&want_term, nterm);
  bits_init(&want_thm, nthm);
  bits_init(&want_inf, ninf);
  for (i = 0; i < nnames; i = j)
  {
    int root = argc <= 1;
    for (j = i; j < nnames && names[j].thm == names[i].thm; j++)
    {
      int k;
      for (k = 1; k < argc && !root; k++)
      {
        root = strlen(argv[k]) == names[j].len &&
               memcmp(argv[k], names[j].name, names[j].len) == 0;
      }
    }
    if (root)
    {
      bits_set(&want_thm, names[i].thm);
    }
  }

  /* Pass 2 */
  cty = ntype;
  ctm = nterm;
  cth = nthm;
  cinf = ninf;
  ctd = ntypedef;
  each_line_backward(pass2_line, NULL);

  /* Pass 3 */
  bits_init(&want_A, ntypedef);
  for (i = 0; i < (size_t)ntypedef; i++)
  {
    if (bits_get(&want_inf, typedefs[i]))
    {
      bits_set(&want_A, (int64_t)i);
    }
  }
  bits_build_rank(&want_type);
  bits_build_rank(&want_term);
  bits_build_rank(&want_thm);
  bits_build_rank(&want_A);
  out_buf = xmalloc(OUT_CHUNK);
  memcpy(out_buf, "HOLTrace 1\n", 11);
  out_len = 11;
  cty = ctm = cth = cinf = ctd = 0;
  each_line_forward(pass3_line, &first);
  out_flush();
  return 0;
}
