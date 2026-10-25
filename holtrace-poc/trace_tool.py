#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: inspect a HOLTrace file (format: holtrace.cr.yp.to/format.html)
# without HOL Light. This does NOT check inferences; it reads the recorded
# objects to answer audit questions:
#
#   summary            line counts per tag, axioms, named theorems
#   axioms             print every axiom (X line)
#   closure NAME       definitions that give meaning to theorem NAME:
#                      constants/types in its statement, closed under
#                      their definitions (C and A lines)
#   show NAME          print the statement of NAME in raw HOL syntax
#   bytes CONST        decode `CONST = [word n; ...]` and print the bytes
#                      as hex, 4 bytes per line (little-endian words)

import sys
from collections import Counter

sys.setrecursionlimit(1000000)


class Trace:
    def __init__(self, path):
        self.types = []  # ('v', name) | ('a', name, args)
        self.terms = []  # ('c', ty, name) | ('d', ty, name) | ('e', ty, f, x) | ('f', ty, v, b)
        self.thms = []  # (hyps, concl)
        self.names = {}  # name -> thm id
        self.axioms = []  # term ids
        self.defs = {}  # const name -> definition term id (v = t)
        self.typedefs = {}  # type name -> (abs, rep, repterm id)
        self.const2typedef = {}  # abs/rep const name -> type name
        self.tags = Counter()
        with open(path, "rb") as f:
            first = f.readline()
            if first != b"HOLTrace 1\n":
                raise Exception("not a HOLTrace 1 file")
            for line in f:
                self._line(line.rstrip(b"\n").decode("ascii"))

    # Argument decoding, relative to the current counter `n`.
    SYM = {
        "!": 1,
        "@": 2,
        "#": 3,
        "$": 4,
        "%": 5,
        "^": 6,
        "&": 7,
        "*": 8,
        "(": 9,
        ")": 10,
    }
    B32 = "0123456789ABCDEFGHIJKLMNOPQRSTUV"

    def _arg(self, s, i, n):
        c = s[i]
        if c in self.SYM:
            return n - self.SYM[c], i + 1
        neg = c == "-"
        if neg:
            i += 1
        j = i
        v = 0
        while j < len(s) and s[j] in self.B32:
            v = 32 * v + self.B32.index(s[j])
            j += 1
        if j == i:
            raise Exception(f"bad argument in {s!r}")
        # A space separates this argument from a following one that starts
        # with a base-32 digit (or from a text argument).
        if j < len(s) and s[j] == " ":
            j += 1
        return (n - v if neg else v), j

    def _args(self, s, n, k=None):
        out = []
        i = 1
        while i < len(s) and (k is None or len(out) < k):
            v, i = self._arg(s, i, n)
            out.append(v)
        return out, s[i:]

    def _line(self, s):
        tag = s[0]
        self.tags[tag] += 1
        nty, ntm, nth = len(self.types), len(self.terms), len(self.thms)
        if tag == "a":
            self.types.append(("v", s[1:]))
        elif tag == "b":
            k, i = self._arg(s, 1, -1)
            args = []
            for _ in range(k):
                a, i = self._arg(s, i, nty)
                args.append(a)
            self.types.append(("a", s[i:], tuple(args)))
        elif tag in "cd":
            ty, i = self._arg(s, 1, nty)
            self.terms.append((tag, ty, s[i:]))
        elif tag in "ef":
            ty, i = self._arg(s, 1, nty)
            a, i = self._arg(s, i, ntm)
            b, i = self._arg(s, i, ntm)
            self.terms.append((tag, ty, a, b))
        elif tag == "t":
            ids, _ = self._args(s, ntm)
            self.thms.append((tuple(ids[:-1]), ids[-1]))
        elif tag == "/":
            th, i = self._arg(s, 1, nth)
            self.names[s[i:]] = th
        elif tag == "X":
            tm, _ = self._arg(s, 1, ntm)
            self.axioms.append(tm)
        elif tag == "C":
            tm, i = self._arg(s, 1, ntm)
            self.defs[s[i:]] = tm
        elif tag == "A":
            _, i = self._arg(s, 1, nty)
            rp, i = self._arg(s, i, ntm)
            _, i = self._arg(s, i, nth)
            w = s[i:].split("]")
            tyname, absname, repname = w[1], w[2], w[3]
            self.typedefs[tyname] = (absname, repname, rp)
            self.const2typedef[absname] = tyname
            self.const2typedef[repname] = tyname

    # ----- term walking

    def symbols(self, roots):
        """Constant names and type names occurring in the given term ids."""
        consts, tynames = set(), set()
        seen_tm, seen_ty = set(), set()
        stack_tm = list(roots)
        stack_ty = []
        while stack_tm or stack_ty:
            if stack_tm:
                t = stack_tm.pop()
                if t in seen_tm:
                    continue
                seen_tm.add(t)
                x = self.terms[t]
                stack_ty.append(x[1])
                if x[0] == "c":
                    consts.add(x[2])
                elif x[0] in "ef":
                    stack_tm += [x[2], x[3]]
            else:
                y = stack_ty.pop()
                if y in seen_ty:
                    continue
                seen_ty.add(y)
                z = self.types[y]
                if z[0] == "a":
                    tynames.add(z[1])
                    stack_ty += list(z[2])
        return consts, tynames

    def closure(self, name):
        hyps, concl = self.thms[self.names[name]]
        todo_c, todo_t = self.symbols(list(hyps) + [concl])
        done_c, done_t = set(), set()
        while todo_c or todo_t:
            if todo_c:
                c = todo_c.pop()
                if c in done_c:
                    continue
                done_c.add(c)
                if c in self.defs:
                    roots = [self.defs[c]]
                elif c in self.const2typedef:
                    todo_t.add(self.const2typedef[c])
                    continue
                else:
                    continue
            else:
                y = todo_t.pop()
                if y in done_t:
                    continue
                done_t.add(y)
                if y not in self.typedefs:
                    continue
                roots = [self.typedefs[y][2]]
            cs, ts = self.symbols(roots)
            todo_c |= cs - done_c
            todo_t |= ts - done_t
        return done_c, done_t

    # ----- decoding

    def dest_comb(self, t):
        x = self.terms[t]
        return (x[2], x[3]) if x[0] == "e" else None

    def const_name(self, t):
        x = self.terms[t]
        return x[2] if x[0] == "c" else None

    def strip_comb(self, t):
        args = []
        while self.terms[t][0] == "e":
            f, a = self.dest_comb(t)
            args.append(a)
            t = f
        return t, args[::-1]

    def numeral(self, t):
        h, args = self.strip_comb(t)
        n = self.const_name(h)
        if n == "NUMERAL" and len(args) == 1:
            return self.numeral(args[0])
        if n == "_0" and not args:
            return 0
        if n in ("BIT0", "BIT1") and len(args) == 1:
            v = self.numeral(args[0])
            return None if v is None else 2 * v + (n == "BIT1")
        return None

    def list_elems(self, t):
        out = []
        while True:
            h, args = self.strip_comb(t)
            n = self.const_name(h)
            if n == "NIL":
                return out
            if n != "CONS" or len(args) != 2:
                return None
            out.append(args[0])
            t = args[1]

    def show(self, t, depth=0, limit=[200000]):
        limit[0] -= 1
        if limit[0] < 0:
            return "..."
        v = self.numeral(t)
        if v is not None:
            return str(v)
        x = self.terms[t]
        if x[0] in "cd":
            return x[2]
        if x[0] == "f":
            return f"(\\{self.show(x[2])}. {self.show(x[3])})"
        h, args = self.strip_comb(t)
        return "(" + " ".join(self.show(a) for a in [h] + args) + ")"


def main():
    path, cmd, *rest = sys.argv[1:]
    tr = Trace(path)
    if cmd == "summary":
        print("tags:", " ".join(f"{k}={v}" for k, v in sorted(tr.tags.items())))
        print(f"types={len(tr.types)} terms={len(tr.terms)} thms={len(tr.thms)}")
        print(
            f"axioms={len(tr.axioms)} definitions={len(tr.defs)} typedefs={len(tr.typedefs)}"
        )
        print("named:", " ".join(sorted(tr.names)))
    elif cmd == "axioms":
        for a in tr.axioms:
            print(tr.show(a))
    elif cmd == "closure":
        cs, ts = tr.closure(rest[0])
        dc = sorted(c for c in cs if c in tr.defs)
        tc = sorted(t for t in ts if t in tr.typedefs)
        print(f"{rest[0]}: {len(dc)} constant definitions, {len(tc)} type definitions")
        prim = sorted(c for c in cs if c not in tr.defs and c not in tr.const2typedef)
        print("primitive constants:", " ".join(prim))
        print("type definitions:", " ".join(tc))
        print("constant definitions:", " ".join(dc))
    elif cmd == "show":
        hyps, concl = tr.thms[tr.names[rest[0]]]
        for h in hyps:
            print("HYP", tr.show(h))
        print(tr.show(concl))
    elif cmd == "bytes":
        d = tr.defs[rest[0]]
        _, rhs = tr.dest_comb(d)
        elems = tr.list_elems(rhs)
        bs = []
        for e in elems:
            h, args = tr.strip_comb(e)
            assert tr.const_name(h) == "word" and len(args) == 1
            bs.append(tr.numeral(args[0]))
        assert all(0 <= b < 256 for b in bs)
        for i in range(0, len(bs), 4):
            print("0x" + "".join(f"{b:02x}" for b in reversed(bs[i : i + 4])))
    else:
        raise SystemExit(f"unknown command {cmd}")


if __name__ == "__main__":
    main()
