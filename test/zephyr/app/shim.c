/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Zephyr entrypoint shim for the mlkem-native tests.
 *
 * Each test provides its own main(), which we rename to mlk_test_main
 * (-Dmain=mlk_test_main on that source) and call from the Zephyr main thread
 * below. Command-line arguments (used by the acvp/wycheproof tests) are read
 * from the host via Arm semihosting SYS_GET_CMDLINE; func/kat take main(void)
 * and ignore them. When the test returns we stop QEMU via a semihosting exit
 * carrying its return code, so the host Makefile sees the pass/fail status.
 */

#include <stddef.h>

extern int mlk_test_main(int argc, char **argv);

/* Arm semihosting operations, trapped by QEMU via `bkpt 0xab`. */
#define MLK_SYS_GET_CMDLINE 0x15
#define MLK_SYS_EXIT_EXTENDED 0x20
#define MLK_ADP_STOPPED_APPLICATION_EXIT 0x20026UL

#define MLK_MAX_ARGS 32
#define MLK_CMDLINE_BUF_SIZE 65536

static long mlk_semihost(unsigned op, void *arg)
{
  register unsigned r0 __asm__("r0") = op;
  register void *r1 __asm__("r1") = arg;
  __asm__ volatile("bkpt 0xab" : "+r"(r0) : "r"(r1) : "memory");
  return (long)r0;
}

static char mlk_cmdline[MLK_CMDLINE_BUF_SIZE];
static char *mlk_argv[MLK_MAX_ARGS + 1];

/* Fetch the host command line via semihosting and split it into argv. */
static int mlk_get_args(char ***argv_out)
{
  struct
  {
    char *buf;
    size_t len;
  } block = {mlk_cmdline, sizeof(mlk_cmdline) - 1};
  int argc = 0;
  char *p = mlk_cmdline;

  *argv_out = mlk_argv;
  if (mlk_semihost(MLK_SYS_GET_CMDLINE, &block) != 0)
  {
    mlk_argv[0] = "test";
    mlk_argv[1] = NULL;
    return 1;
  }

  while (*p != '\0' && argc < MLK_MAX_ARGS)
  {
    while (*p == ' ' || *p == '\t')
    {
      p++;
    }
    if (*p == '\0')
    {
      break;
    }
    mlk_argv[argc++] = p;
    while (*p != '\0' && *p != ' ' && *p != '\t')
    {
      p++;
    }
    if (*p != '\0')
    {
      *p++ = '\0';
    }
  }
  mlk_argv[argc] = NULL;
  return argc;
}

static void mlk_semihost_exit(int code)
{
  unsigned long block[2] = {MLK_ADP_STOPPED_APPLICATION_EXIT,
                            (unsigned long)code};
  mlk_semihost(MLK_SYS_EXIT_EXTENDED, block);
}

int main(void)
{
  char **argv;
  int argc = mlk_get_args(&argv);
  int rc = mlk_test_main(argc, argv);
  mlk_semihost_exit(rc);
  return rc;
}
