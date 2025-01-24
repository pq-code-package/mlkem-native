[//]: # (SPDX-License-Identifier: CC-BY-4.0)

This patch to Valgrind allows detecting secret-dependent division
instructions by flagging variable-latency instruction depending
on uninitialized data.

It is part of the paper
KyberSlash: Exploiting secret-dependent division timings in Kyber implementations
by
- Daniel J. Bernstein
- Karthikeyan Bhargavan
- Shivam Bhasin
- Anupam Chattopadhyay
- Tee Kiah Chia
- Matthias J. Kannwischer
- Franziskus Kiefer
- Thales Paiva
- Prasanna Ravi
- Goutam Tamvada

See [https://kyberslash.cr.yp.to/papers.html](https://kyberslash.cr.yp.to/papers.html).
