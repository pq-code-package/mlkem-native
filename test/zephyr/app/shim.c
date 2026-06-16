/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Zephyr entrypoint shim for the mlkem-native tests.
 *
 * Each test's main() is renamed to mlk_test_main (-Dmain=mlk_test_main) and
 * called from here. argv is fetched from the host via semihosting (needed by
 * the acvp/wycheproof tests); on return we exit QEMU with the test's return
 * code, again via semihosting.
 */

#include <stddef.h>

extern int mlk_test_main(int argc, char **argv);

/* Arm semihosting operations, trapped by QEMU via `bkpt 0xab`. */
#define SYS_GET_CMDLINE 0x15
#define SYS_EXIT_EXTENDED 0x20
#define ADP_STOPPED_APPLICATION_EXIT 0x20026UL

#define MAX_ARGS 32
#define CMDLINE_BUF_SIZE 65536

static long semihost(unsigned op, void *arg)
{
  register unsigned r0 __asm__("r0") = op;
  register void *r1 __asm__("r1") = arg;
  __asm__ volatile("bkpt 0xab" : "+r"(r0) : "r"(r1) : "memory");
  return (long)r0;
}

static char cmdline[CMDLINE_BUF_SIZE];
static char *argv_buf[MAX_ARGS + 1];

/* Fetch the host command line via semihosting and split it into argv. */
static int get_args(char ***argv_out)
{
  struct
  {
    char *buf;
    size_t len;
  } block = {cmdline, sizeof(cmdline) - 1};
  int argc = 0;
  char *p = cmdline;

  *argv_out = argv_buf;
  if (semihost(SYS_GET_CMDLINE, &block) != 0)
  {
    argv_buf[0] = "test";
    argv_buf[1] = NULL;
    return 1;
  }

  while (*p != '\0' && argc < MAX_ARGS)
  {
    while (*p == ' ' || *p == '\t')
    {
      p++;
    }
    if (*p == '\0')
    {
      break;
    }
    argv_buf[argc++] = p;
    while (*p != '\0' && *p != ' ' && *p != '\t')
    {
      p++;
    }
    if (*p != '\0')
    {
      *p++ = '\0';
    }
  }
  argv_buf[argc] = NULL;
  return argc;
}

static void semihost_exit(int code)
{
  unsigned long block[2] = {ADP_STOPPED_APPLICATION_EXIT, (unsigned long)code};
  semihost(SYS_EXIT_EXTENDED, block);
}

int main(void)
{
  char **argv;
  int argc = get_args(&argv);
  int rc = mlk_test_main(argc, argv);
  semihost_exit(rc);
  return rc;
}
