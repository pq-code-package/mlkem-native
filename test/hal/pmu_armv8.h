/*
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* Compatibility wrapper: CMSIS uses armv8m_pmu.h under m-profile */
#if defined(__ARM_ARCH_8M_MAIN__) || defined(__ARM_ARCH_8_1M_MAIN__)
#include <m-profile/armv8m_pmu.h>
#else
#error pmu_armv8.h included on non Armv8-M build
#endif
