# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

cmake_minimum_required(VERSION 3.20.0)
find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(mlkem_native_zephyr)

# Parameters supplied via -D from platform.mk:
#   ZEPHYR_NATIVE_ROOT - mlkem-native checkout the test is built from
#   ZEPHYR_TEST_SRCS   - test sources (entrypoint + support, e.g. notrandombytes
#                        and -- for bench -- the HAL), relative to
#                        ZEPHYR_NATIVE_ROOT, space separated
#   ZEPHYR_TEST_CFLAGS - the test binary's CFLAGS (see below); includes the
#                        parameter set (-DMLK_CONFIG_PARAMETER_SET=...)
set(R ${ZEPHYR_NATIVE_ROOT})

separate_arguments(_test_srcs UNIX_COMMAND "${ZEPHYR_TEST_SRCS}")
list(TRANSFORM _test_srcs PREPEND ${R}/)

target_sources(app PRIVATE
  ${R}/mlkem/mlkem_native.c
  ${_test_srcs}
)

target_include_directories(app PRIVATE
  ${R}/mlkem
  ${R}/test/notrandombytes
  ${R}/test/hal
)

# The Zephyr shim owns main() (see below). On QEMU targets shim.c stops the
# emulator with the test's exit code; the NUCLEO-N657X0-Q hardware target needs
# its own shim plus libc wrappers that route stdio over ITM/SWO.
if(ZEPHYR_NUCLEO_N657X0_Q)
  # The STM32N6 SystemInit() fallback derives VTOR from &g_pfnVectors. With
  # Zephyr data in DTCM that symbol lives in RAM, so force VTOR to the ITCM
  # vector table instead.
  zephyr_compile_definitions(
    USER_VECT_TAB_ADDRESS
    VECT_TAB_BASE_ADDRESS=0x10000000
    VECT_TAB_OFFSET=0x0
  )
  target_sources(app PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/shim_nucleo_n657x0_q.c)
  target_compile_definitions(app PRIVATE
    printf=__wrap_printf
    fprintf=__wrap_fprintf
    puts=__wrap_puts
    putchar=__wrap_putchar
    fflush=__wrap_fflush
    exit=__wrap_exit
  )
  target_link_options(app PRIVATE
    -Wl,--wrap=printf
    -Wl,--wrap=fprintf
    -Wl,--wrap=puts
    -Wl,--wrap=putchar
    -Wl,--wrap=fflush
    -Wl,--wrap=exit
  )
else()
  target_sources(app PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/shim.c)
endif()

# The test binary's CFLAGS, forwarded from the build (test/zephyr/platform.mk
# assembles and escapes them) and applied to the mlkem amalgamation and the test
# sources alike, so both honour the project's own warning/opt/std policy and
# per-test feature defines rather than a divergent Zephyr default.
if(ZEPHYR_TEST_CFLAGS)
  separate_arguments(_cflags UNIX_COMMAND "${ZEPHYR_TEST_CFLAGS}")
  target_compile_options(app PRIVATE ${_cflags})
endif()

# The benchmark HAL is the only test source that pulls in Zephyr SDK headers
# (<zephyr/kernel.h> for the cycle counter). Those headers are not clean under
# the project's strict, -Werror'd warning set forwarded above (e.g.
# -Wconversion, -Wsign-conversion, -pedantic), so drop -Werror just for this
# file -- our own sources stay strict.
set_source_files_properties(${R}/test/hal/hal.c
  PROPERTIES COMPILE_OPTIONS "-Wno-error")

set_source_files_properties(${CMAKE_CURRENT_SOURCE_DIR}/shim_nucleo_n657x0_q.c
  PROPERTIES COMPILE_OPTIONS "-Wno-error")

# Optional native FIPS202 backend (e.g. Armv8.1-M MVE on Cortex-M55). The
# monolithic mlkem_native.c already includes the backend C sources; its
# assembly counterpart comes from mlkem_native_asm.S.
if(ZEPHYR_FIPS202_BACKEND)
  target_sources(app PRIVATE ${R}/mlkem/mlkem_native_asm.S)
  target_compile_definitions(app PRIVATE
    MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
    "MLK_CONFIG_FIPS202_BACKEND_FILE=\"${ZEPHYR_FIPS202_BACKEND}\"")
endif()

# Each test brings its own int main(void); rename it so the selected Zephyr
# shim owns main() and can return the test's exit code through the target's
# runner. Only the test entrypoint in ZEPHYR_TEST_SRCS defines main(); the
# support sources (notrandombytes, hal) don't, so applying the define to all is
# harmless.
set_source_files_properties(${_test_srcs}
  PROPERTIES COMPILE_DEFINITIONS "main=mlk_test_main")
