#!@bash@
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
# shellcheck shell=bash disable=SC2239

set -eu

cd @candle@/candle/build
exec ./cake --candle "$@"
