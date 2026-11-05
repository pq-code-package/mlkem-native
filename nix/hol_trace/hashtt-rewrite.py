#!@python3@
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# Rewrite OCaml sources in place for HOLTrace's hashtt mode.
#
# hashtt adds a cached hash to every HOL Light type, term and theorem
# constructor (Comb of term * term * int, ...). Code that matches on the
# constructors must then ignore the extra field: Comb(f,x) becomes
# Comb(f,x,_). HOLTrace's installer rewrites the HOL Light sources this
# way; this tool applies the same rewrite (`process` from the patched
# install-worker) to other code, i.e. s2n-bignum and our proofs.
#
# Usage: holtrace-hashtt-rewrite DIR...

import importlib.machinery
import importlib.util
import os
import sys

INSTALL_WORKER = "@installWorker@"


def load_install_worker():
    loader = importlib.machinery.SourceFileLoader("install_worker", INSTALL_WORKER)
    spec = importlib.util.spec_from_loader("install_worker", loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


def main():
    worker = load_install_worker()
    changed = 0
    for top in sys.argv[1:]:
        for d, _, files in os.walk(top):
            for fn in files:
                if not fn.endswith(".ml"):
                    continue
                path = os.path.join(d, fn)
                with open(path, encoding="latin-1") as f:
                    old = f.read()
                new = worker.process(old)
                if new != old:
                    with open(path, "w", encoding="latin-1") as f:
                        f.write(new)
                    changed += 1
    print(f"hashtt rewrite: {changed} files changed")


if __name__ == "__main__":
    main()
