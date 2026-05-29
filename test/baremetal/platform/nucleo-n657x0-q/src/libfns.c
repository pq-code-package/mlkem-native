/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <errno.h>
#include <sys/stat.h>

int __wrap__close(int fd);
int __wrap__fstat(int fd, struct stat *buf);
int __wrap__getpid(void);
int __wrap__isatty(int fd);
int __wrap__lseek(int fd, int offset, int whence);
int __wrap__kill(int pid, int sig);


int __wrap__close(int fd)
{
  (void)fd;
  return 0;
}

int __wrap__fstat(int fd, struct stat *buf)
{
  (void)fd;
  (void)buf;
  errno = ENOSYS;
  return -1;
}

int __wrap__getpid(void)
{
  errno = ENOSYS;
  return -1;
}

int __wrap__isatty(int fd)
{
  (void)fd;
  errno = ENOSYS;
  return -1;
}

int __wrap__lseek(int fd, int offset, int whence)
{
  (void)fd;
  (void)offset;
  (void)whence;
  errno = ENOSYS;
  return -1;
}

int __wrap__kill(int pid, int sig)
{
  (void)pid;
  (void)sig;
  errno = ENOSYS;
  return -1;
}
