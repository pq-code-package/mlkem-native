/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#define MLKEM_NATIVE_CONFIG_FILE "config_a.h"
#include "mlkem_native_all.c"
#undef MLKEM_NATIVE_CONFIG_FILE

int main(void)
{
  /* Nothing to do here -- only test that it builds */
  return 0;
}
