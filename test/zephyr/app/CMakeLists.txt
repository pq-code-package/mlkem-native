# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

cmake_minimum_required(VERSION 3.20.0)
find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(mlkem_native_zephyr)

# Parameters supplied via -D from platform.mk:
#   ZEPHYR_NATIVE_ROOT - mlkem-native checkout the test is built from
#   ZEPHYR_LEVEL       - ML-KEM parameter set: 512 | 768 | 1024
#   ZEPHYR_TEST_SRC    - test entrypoint, relative to ZEPHYR_NATIVE_ROOT
#   ZEPHYR_TEST_DEFS   - optional extra -D defines (space separated)
set(R ${ZEPHYR_NATIVE_ROOT})

target_sources(app PRIVATE
  ${R}/mlkem/mlkem_native.c
  ${R}/${ZEPHYR_TEST_SRC}
  ${R}/test/notrandombytes/notrandombytes.c
  ${CMAKE_CURRENT_SOURCE_DIR}/shim.c
)

target_include_directories(app PRIVATE
  ${R}/mlkem
  ${R}/test/notrandombytes
)

target_compile_definitions(app PRIVATE MLK_CONFIG_PARAMETER_SET=${ZEPHYR_LEVEL})

if(ZEPHYR_TEST_DEFS)
  separate_arguments(_defs UNIX_COMMAND "${ZEPHYR_TEST_DEFS}")
  target_compile_definitions(app PRIVATE ${_defs})
endif()

# Optional native FIPS202 backend (e.g. Armv8.1-M MVE on Cortex-M55). The
# monolithic mlkem_native.c already includes the backend C sources; its
# assembly counterpart comes from mlkem_native_asm.S.
if(ZEPHYR_FIPS202_BACKEND)
  target_sources(app PRIVATE ${R}/mlkem/mlkem_native_asm.S)
  target_compile_definitions(app PRIVATE
    MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202
    "MLK_CONFIG_FIPS202_BACKEND_FILE=\"${ZEPHYR_FIPS202_BACKEND}\"")
endif()

# The bench tests need the cycle-counting HAL.
if(ZEPHYR_TEST_HAL)
  target_sources(app PRIVATE ${R}/test/hal/hal.c)
  target_include_directories(app PRIVATE ${R}/test/hal)
endif()

# Each test brings its own int main(void); rename it so the Zephyr shim
# (shim.c) owns main() and can stop QEMU with the test's exit code.
set_source_files_properties(${R}/${ZEPHYR_TEST_SRC}
  PROPERTIES COMPILE_DEFINITIONS "main=mlk_test_main")
