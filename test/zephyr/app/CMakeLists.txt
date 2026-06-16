# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

cmake_minimum_required(VERSION 3.20.0)
find_package(Zephyr REQUIRED HINTS $ENV{ZEPHYR_BASE})
project(mlkem_native_zephyr)

# Parameters supplied via -D from platform.mk:
#   MLKEM_NATIVE_ROOT - mlkem-native checkout the test is built from
#   MLK_LEVEL         - ML-KEM parameter set: 512 | 768 | 1024
#   MLK_TEST_SRC      - test entrypoint, relative to MLKEM_NATIVE_ROOT
#   MLK_TEST_DEFS     - optional extra -D defines (space separated)
set(R ${MLKEM_NATIVE_ROOT})

target_sources(app PRIVATE
  ${R}/mlkem/mlkem_native.c
  ${R}/${MLK_TEST_SRC}
  ${R}/test/notrandombytes/notrandombytes.c
  ${CMAKE_CURRENT_SOURCE_DIR}/shim.c
)

target_include_directories(app PRIVATE
  ${R}/mlkem
  ${R}/test/notrandombytes
)

target_compile_definitions(app PRIVATE MLK_CONFIG_PARAMETER_SET=${MLK_LEVEL})

if(MLK_TEST_DEFS)
  separate_arguments(_mlk_defs UNIX_COMMAND "${MLK_TEST_DEFS}")
  target_compile_definitions(app PRIVATE ${_mlk_defs})
endif()

# Each test brings its own int main(void); rename it so the Zephyr shim
# (shim.c) owns main() and can stop QEMU with the test's exit code.
set_source_files_properties(${R}/${MLK_TEST_SRC}
  PROPERTIES COMPILE_DEFINITIONS "main=mlk_test_main")
