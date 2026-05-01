/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <errno.h>
#include <stdint.h>
#include <stdio.h>

#define NUCLEO_STDOUT_CAPTURE_SIZE (1536U * 1024U)

__attribute__((aligned(32), used, section(".stdout_capture")))
volatile uint8_t nucleo_stdout_capture[NUCLEO_STDOUT_CAPTURE_SIZE];

__attribute__((used))
volatile uint32_t nucleo_stdout_capture_len;

__attribute__((used))
volatile uint32_t nucleo_stdout_capture_truncated;

int _write(int fd, char *src, int length) {
  (void)fd;

  if (src == NULL || length < 0) {
    errno = EINVAL;
    return -1;
  }

  uint32_t offset = nucleo_stdout_capture_len;
  if (offset < NUCLEO_STDOUT_CAPTURE_SIZE) {
    uint32_t available = NUCLEO_STDOUT_CAPTURE_SIZE - offset;
    uint32_t written = (uint32_t)length;
    if (written > available) {
      written = available;
      nucleo_stdout_capture_truncated = 1;
    }

    for (uint32_t idx = 0; idx < written; idx++) {
      nucleo_stdout_capture[offset + idx] = (uint8_t)src[idx];
    }
    nucleo_stdout_capture_len = offset + written;
  } else if (length > 0) {
    nucleo_stdout_capture_truncated = 1;
  }

  return length;
}

void nucleo_stdio_init(void) {
  setvbuf(stdout, NULL, _IONBF, 0);
  setvbuf(stderr, NULL, _IONBF, 0);
}
