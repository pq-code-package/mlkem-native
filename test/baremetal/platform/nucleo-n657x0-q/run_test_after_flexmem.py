#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import os
import sys


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    wrapper = os.path.join(here, "exec_wrapper.py")
    os.execv(sys.executable, [sys.executable, wrapper] + sys.argv[1:])


if __name__ == "__main__":
    main()
