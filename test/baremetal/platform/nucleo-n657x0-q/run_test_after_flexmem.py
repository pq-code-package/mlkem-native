#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Compatibility entry point for running a test after FLEXMEM configuration."""

import os
import sys


def main():
    """Replace this process with ``exec_wrapper.py`` while preserving argv."""
    here = os.path.dirname(os.path.abspath(__file__))
    wrapper = os.path.join(here, "exec_wrapper.py")
    # os.execv keeps make/CI process trees simple: this shim does not need to
    # proxy signals, streams, or exit status from a child process.
    os.execv(sys.executable, [sys.executable, wrapper] + sys.argv[1:])


if __name__ == "__main__":
    main()
