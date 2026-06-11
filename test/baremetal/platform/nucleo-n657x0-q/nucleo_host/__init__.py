# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""
Host-side helpers for the NUCLEO-N657X0-Q baremetal platform.

The modules in this package keep debugger orchestration details out of the
entry-point scripts.  They are intentionally small and mostly pure so the
hardware-independent pieces can be covered by local unit tests.
"""
