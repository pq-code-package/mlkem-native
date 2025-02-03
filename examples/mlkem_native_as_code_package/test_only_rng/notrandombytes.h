/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: LicenseRef-PD-hp OR CC0-1.0 OR 0BSD OR MIT-0 OR MI
 * Based on https://cr.yp.to/papers.html#surf by Daniel. J. Bernstein
 */
#ifndef NOTRANDOMBYTES_H
#define NOTRANDOMBYTES_H

#include <stdint.h>
#include <stdlib.h>

/**
 * WARNING
 *
 * The randombytes() implementation in this file is for TESTING ONLY.
 * You MUST NOT use this implementation outside of testing.
 *
 */

void randombytes_reset(void);
void randombytes(uint8_t *buf, size_t n);

#endif /* NOTRANDOMBYTES_H */
