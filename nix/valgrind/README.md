[//]: # (SPDX-License-Identifier: CC-BY-4.0)

This patch to Valgrind allows detecting secret-dependent division
instructions by flagging variable-latency instruction depending
on uninitialized data.

It is part of the paper [@KYBERSLASH].
