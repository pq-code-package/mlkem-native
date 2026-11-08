# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Check a replay result against the accepted definitions and statements.

A replay backend rebuilds a trace's theorems in its own kernel and writes
the kernel's axioms, constant definitions and type definitions, and the
requested named theorems (format and backend guarantees:
term_encoding.ml). This module decides whether that result is
acceptable:

1. Starting from the axioms and the named theorems, it collects every
   constant and type that they mention, follows each to its definition, and
   repeats for the definition bodies. Definitions that are not reached do
   not affect what the theorems mean: HOL Light's definitions are
   conservative.
2. Every reached constant and type must have a definition, except the
   kernel primitives `=`, `@`, `bool`, `fun` and `ind`.
3. Every reached definition must equal an accepted one.
4. Every axiom must be in the HOL Light layer (accepted/base/hol_light.defs),
   and every named theorem must equal its accepted statement.

Kernel objects are compared through their rendering, a deterministic and
unambiguous text form that is also what the accepted files
(accepted/{base,spec,proofs}) store for review.

This module knows nothing about object files. A definition of a byte
list is written with a comment giving its length and SHA-256; check-binary
compares the byte lists with functions in binaries.
"""

import hashlib
import json
import os
import re

RESULT_MAGIC = b"HOLTRACE-RESULT-5\n"
# Constants and types that have no definition. Every backend must declare
# them itself, with HOL Light's types and arities, before replaying: a
# trace cannot declare them. The renderer relies on the generic types of
# `=` and `@` given in Theory.generic.
PRIMITIVE_CONSTANTS = {"=", "@"}
PRIMITIVE_TYPES = {"bool", "fun", "ind"}
# Renderings longer than this are stored as their SHA-256 hash. Today only
# s2n-bignum's instruction decoders and execution functions, its x86
# `instruction` type and its arm `__opaque_bitmatch_3` are that large;
# they are trusted through the s2n-bignum pin.
LARGE = 1 << 16
HASHED = "sha256 "


class Failed(Exception):
    pass


# ----- kernel objects
#
# Types:    ("v", name) | ("t", name, (args...))
# Terms:    ("v", name, type) | ("c", name, type) |
#           ("a", function, argument) | ("l", variable, body)
# Theorems: (hypotheses, conclusion)

BOOL = ("t", "bool", ())
NUM = ("t", "num", ())
INT = ("t", "int", ())


def fun(a, b):
    return ("t", "fun", (a, b))


def list_of(a):
    return ("t", "list", (a,))


def is_fun(ty):
    return ty[0] == "t" and ty[1] == "fun" and len(ty[2]) == 2


def is_prod(ty):
    return ty[0] == "t" and ty[1] == "prod" and len(ty[2]) == 2


BYTE = (
    "t",
    "word",
    (("t", "tybit0", (("t", "tybit0", (("t", "tybit0", (("t", "1", ()),)),)),)),),
)
BYTE_WORD = ("c", "word", fun(NUM, BYTE))
BYTE_CONS = ("c", "CONS", fun(BYTE, fun(list_of(BYTE), list_of(BYTE))))


def type_vars(ty, out):
    stack = [ty]
    while stack:
        t = stack.pop()
        if t[0] == "v":
            out.add(t[1])
        else:
            stack.extend(t[2])
    return out


class TypeOf:
    """type_of for terms, memoized per term object."""

    def __init__(self):
        self.memo = {}

    def __call__(self, tm):
        key = id(tm)
        if key in self.memo:
            return self.memo[key][1]
        if tm[0] in "vc":
            ty = tm[2]
        elif tm[0] == "l":
            ty = fun(tm[1][2], self(tm[2]))
        else:
            fty = self(tm[1])
            if not is_fun(fty):
                raise Failed("ill-typed combination in replay result")
            ty = fty[2][1]
        # Keep tm alive so that id(tm) stays unique.
        self.memo[key] = (tm, ty)
        return ty


# ----- replay result


class Reader:
    """The theorem encoding of term_encoding.ml: a prefix code."""

    def __init__(self, data, pos=0):
        self.data, self.pos = data, pos
        self.types = {}

    def char(self):
        if self.pos >= len(self.data):
            raise Failed("replay result is truncated")
        c = chr(self.data[self.pos])
        self.pos += 1
        return c

    def count(self):
        start = self.pos
        while self.pos < len(self.data) and self.data[self.pos] != ord(":"):
            self.pos += 1
        digits = self.data[start : self.pos]
        if self.pos >= len(self.data) or not digits.isdigit() or len(digits) > 12:
            raise Failed("bad count in replay result")
        self.pos += 1
        return int(digits)

    def raw(self):
        n = self.count()
        if self.pos + n > len(self.data):
            raise Failed("replay result is truncated")
        s = self.data[self.pos : self.pos + n].decode("latin-1")
        self.pos += n
        return s

    def type(self):
        c = self.char()
        if c == "v":
            ty = ("v", self.raw())
        elif c == "t":
            name = self.raw()
            ty = ("t", name, tuple(self.type() for _ in range(self.count())))
        else:
            raise Failed("bad type in replay result")
        return self.types.setdefault(ty, ty)

    def term(self):
        # Iterative: byte lists nest thousands of combinations deep.
        stack = []
        while True:
            c = self.char()
            if c in "vc":
                node = (c, self.raw(), self.type())
            elif c in "al":
                stack.append([c, None])
                continue
            else:
                raise Failed("bad term in replay result")
            while stack:
                frame = stack[-1]
                if frame[1] is None:
                    frame[1] = node
                    break
                if frame[0] == "l" and frame[1][0] != "v":
                    raise Failed("abstraction over a non-variable")
                node = (frame[0], frame[1], node)
                stack.pop()
            else:
                return node

    def theorem(self):
        if self.char() != "h":
            raise Failed("bad theorem in replay result")
        hyps = tuple(self.term() for _ in range(self.count()))
        return hyps, self.term()


def read_result(path):
    """Return (axioms, definitions, typedefs, named) from a result file."""
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError as e:
        raise Failed(f"cannot read replay result: {e}") from e
    if not data.startswith(RESULT_MAGIC):
        raise Failed("replay result has no valid header")
    r = Reader(data, len(RESULT_MAGIC))
    axioms, definitions, typedefs, named = [], [], [], []
    while True:
        tag = r.char()
        if tag == "S":
            break
        if tag == "F":
            raise Failed(r.raw())
        if tag == "X":
            axioms.append(r.theorem())
        elif tag == "D":
            definitions.append(r.theorem())
        elif tag == "Y":
            typedefs.append(r.theorem())
        elif tag == "T":
            named.append((r.raw(), r.theorem()))
        else:
            raise Failed(f"bad record {tag!r} in replay result")
    if r.pos != len(data):
        raise Failed("replay result continues after its end record")
    return axioms, definitions, typedefs, named


# ----- the theory


def dest_eq(tm):
    if tm[0] == "a" and tm[1][0] == "a" and tm[1][1][0] == "c":
        if tm[1][1][1] == "=":
            return tm[1][2], tm[2]
    return None


def dest_typedef(th):
    """(type name, abs, rep) of a type definition's theorem
    |- P r = (rep (abs r) = r)."""
    outer = dest_eq(th[1]) if not th[0] else None
    inner = dest_eq(outer[1]) if outer else None
    if (
        inner is None
        or inner[0][0] != "a"
        or inner[0][1][0] != "c"
        or inner[0][2][0] != "a"
        or inner[0][2][1][0] != "c"
    ):
        raise Failed("replay result has a malformed type definition")
    rep, abs_ = inner[0][1], inner[0][2][1]
    abs_type = abs_[2][2][1]
    if abs_type[0] != "t":
        raise Failed("replay result has a malformed type definition")
    return abs_type[1], abs_, rep


class Theory:
    """Definitions and type definitions indexed by what they define."""

    def __init__(self, definitions, typedefs):
        self.const_def = {}  # constant name -> definition theorem
        self.type_def = {}  # type name -> type-definition theorem
        self.typedef_of_const = {}  # abs/rep constant -> type name
        self.typedef_consts = {}  # type name -> (abs, rep) names
        # Generic types, for rendering: constant name -> type
        self.generic = {
            "=": fun(("v", "A"), fun(("v", "A"), BOOL)),
            "@": fun(fun(("v", "A"), BOOL), ("v", "A")),
        }
        for th in definitions:
            eq = dest_eq(th[1]) if not th[0] else None
            if eq is None or eq[0][0] != "c":
                raise Failed("replay result has a malformed definition")
            name = eq[0][1]
            if name in self.const_def or name in PRIMITIVE_CONSTANTS:
                raise Failed(f"constant {name} is defined twice")
            self.const_def[name] = th
            self.generic[name] = eq[0][2]
        for th in typedefs:
            tyname, abs_, rep = dest_typedef(th)
            if tyname in self.type_def or tyname in PRIMITIVE_TYPES:
                raise Failed(f"type {tyname} is defined twice")
            self.type_def[tyname] = th
            self.typedef_consts[tyname] = (abs_[1], rep[1])
            for c in (abs_, rep):
                if c[1] in self.generic or c[1] in self.typedef_of_const:
                    raise Failed(f"constant {c[1]} is defined twice")
                self.typedef_of_const[c[1]] = tyname
                self.generic[c[1]] = c[2]

    def closure(self, roots):
        """Definitions and type definitions that the roots depend on."""
        consts, types, errors = set(), set(), []
        todo = [tm for hyps, concl in roots for tm in (*hyps, concl)]
        seen_types = set()

        def visit_type(ty):
            stack = [ty]
            while stack:
                t = stack.pop()
                if t in seen_types:
                    continue
                seen_types.add(t)
                if t[0] == "t":
                    stack.extend(t[2])
                    if t[1] not in types:
                        types.add(t[1])
                        if t[1] in self.type_def:
                            todo.append(self.type_def[t[1]][1])
                        elif t[1] not in PRIMITIVE_TYPES:
                            errors.append(f"type {t[1]} has no definition")

        seen_terms = set()
        while todo:
            tm = todo.pop()
            if id(tm) in seen_terms:
                continue
            seen_terms.add(id(tm))
            if tm[0] in "al":
                todo.extend((tm[1], tm[2]))
                continue
            visit_type(tm[2])
            if tm[0] == "c" and tm[1] not in consts:
                name = tm[1]
                consts.add(name)
                if name in self.const_def:
                    todo.append(self.const_def[name][1])
                elif name in self.typedef_of_const:
                    visit_type(("t", self.typedef_of_const[name], ()))
                elif name not in PRIMITIVE_CONSTANTS:
                    errors.append(f"constant {name} has no definition")
        if errors:
            raise Failed("; ".join(sorted(set(errors))))
        return (
            {n: self.const_def[n] for n in consts if n in self.const_def},
            {n: self.type_def[n] for n in types if n in self.type_def},
        )


# ----- rendering
#
# Kernel objects are printed as fully parenthesized prefix expressions:
#
#   (f a b)          application of f to a and b
#   (\x:ty. body)    abstraction
#   x                the variable bound by the innermost binder named x
#   {x:ty}           any other variable, e.g. a free one
#   c, c:ty          a constant; the type is shown unless it follows
#                    from the constant's generic type and its arguments
#   $c, $c:ty        a constant whose name is bound by an enclosing binder
#   _1, _2, ...      variables named _<digits> (HOL Light's genvars),
#                    renumbered in order of first occurrence
#   '?1, '?2, ...    type variables named ?<digits> (invented by the
#                    parser), renumbered likewise
#   #12              a numeral NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 _0))))
#   &12              an integer literal int_of_num #12
#   [a; b]           CONS a (CONS b NIL)
#   #x[0a ff]        [word 10; word 255] : (word 8) list, every element
#                    `word n` with a canonical numeral n < 256
#   'A               a type variable
#   (a -> b -> c)    a function type
#   (a # b # c)      a product type prod a (prod b c)
#   (list num)       a type constructor applied to arguments
#   #64              a numeral type (tybit0 (... 1))
#
# Names are printed raw if they are alphanumeric, or symbolic and not
# the name of a variable or type variable, and as JSON strings otherwise:
# a variable named + is "+" in its binder and in the body. Equal text
# implies equal kernel objects, up to the renumbering of genvars: a
# reviewer who reads the text reads exactly the object that is compared.

RAW_ALNUM = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_']*\Z")
RAW_SYMBOL = re.compile(r"[!#%&*+,\-/<=>?@\\^|~]+\Z")
RESERVED = {"\\", "->", "#", "|-"}
GENVAR = re.compile(r"_[0-9]+\Z")
GENTYVAR = re.compile(r"\?[0-9]+\Z")
WIDTH = 100
# Binder constants, applied to an abstraction, are printed (!x:ty. body).
BINDERS = {"!", "?", "?!", "@"}
# Right-nested applications of these constants are printed as one:
# (/\ a (/\ b c)) as (/\ a b c). That is unambiguous because each takes
# two arguments and returns no function, so (/\ a b c) cannot mean
# anything else.
CHAINS = {"/\\", "\\/", "==>", ","}


def qname(name, symbols=True):
    if RAW_ALNUM.match(name) or (
        symbols and RAW_SYMBOL.match(name) and name not in RESERVED
    ):
        return name
    return json.dumps(name)


def finty(ty):
    """The number denoted by a numeral type, or None."""
    bits = []
    while ty[0] == "t" and ty[1] in ("tybit0", "tybit1") and len(ty[2]) == 1:
        bits.append(ty[1] == "tybit1")
        ty = ty[2][0]
    if not bits or ty != ("t", "1", ()):
        return None
    n = 1
    for bit in reversed(bits):
        n = 2 * n + bit
    return n


def render_type(ty, tyvars={}):
    """tyvars renames type variables; see Renderer.number_generated."""
    if ty[0] == "v":
        name = tyvars.get(ty[1], ty[1])
        return "'" + (name if GENTYVAR.match(name) else qname(name, symbols=False))
    n = finty(ty)
    if n is not None:
        return f"#{n}"
    for infix, test in ((" -> ", is_fun), (" # ", is_prod)):
        if test(ty):
            parts = []
            while test(ty):
                parts.append(ty[2][0])
                ty = ty[2][1]
            parts.append(ty)
            return "(" + infix.join(render_type(p, tyvars) for p in parts) + ")"
    if not ty[2]:
        return qname(ty[1])
    args = [render_type(a, tyvars) for a in ty[2]]
    return "(" + " ".join([qname(ty[1])] + args) + ")"


def numeral(tm):
    """The number denoted by a canonical NUMERAL term, or None."""
    if tm[0] != "a" or tm[1] != ("c", "NUMERAL", fun(NUM, NUM)):
        return None
    bits, tm = [], tm[2]
    while tm[0] == "a" and tm[1][0] == "c" and tm[1][1] in ("BIT0", "BIT1"):
        if tm[1][2] != fun(NUM, NUM):
            return None
        bits.append(tm[1][1] == "BIT1")
        tm = tm[2]
    if tm != ("c", "_0", NUM) or (bits and not bits[-1]):
        return None
    n = 0
    for bit in reversed(bits):
        n = 2 * n + bit
    return n


class Doc:
    """A layout unit: an atom, an abstraction "(\\x:ty. body)", or a
    delimited sequence: an application "(head args...)", a list
    "[a; b]" or a byte list "#x[0a 1b]"."""

    __slots__ = ("kind", "text", "items", "width")
    # kind -> (opening, separator, closing, indent of continuation lines)
    DELIMITERS = {
        "app": ("(", " ", ")", 2),
        "list": ("[", "; ", "]", 1),
        "bytes": ("#x[", " ", "]", 3),
    }

    def __init__(self, kind, text="", items=()):
        self.kind, self.text, self.items = kind, text, items
        if kind == "atom":
            self.width = len(text)
        elif kind == "abs":
            self.width = len(text) + 2 + items[0].width
        else:
            opening, sep, closing, _ = self.DELIMITERS[kind]
            self.width = (
                len(opening)
                + sum(i.width for i in items)
                + len(sep) * (len(items) - 1)
                + len(closing)
            )

    def flat(self, out):
        if self.kind == "atom":
            out.append(self.text)
        elif self.kind == "abs":
            out.append(self.text + " ")
            self.items[0].flat(out)
            out.append(")")
        else:
            opening, sep, closing, _ = self.DELIMITERS[self.kind]
            out.append(opening)
            for k, item in enumerate(self.items):
                if k:
                    out.append(sep)
                item.flat(out)
            out.append(closing)

    def lines(self, indent, out):
        """Append to out, a list of lines; the first continues out[-1].
        A unit that does not fit is broken: a delimited sequence keeps as
        many items on a line as fit, and puts an item that it has to
        break, and everything after it, on new lines; an abstraction puts
        its body on a new line."""
        if self.kind == "atom" or indent + self.width <= WIDTH:
            parts = []
            self.flat(parts)
            out[-1] += "".join(parts)
        elif self.kind == "abs":
            out[-1] += self.text
            out.append(" " * (indent + 2))
            self.items[0].lines(indent + 2, out)
            out[-1] += ")"
        else:
            opening, sep, closing, cont = self.DELIMITERS[self.kind]
            out[-1] += opening
            self.items[0].lines(indent + len(opening), out)
            broken = False
            for item in self.items[1:]:
                if not broken and len(out[-1]) + len(sep) + item.width <= WIDTH:
                    out[-1] += sep
                    item.lines(indent + cont, out)
                else:
                    out[-1] += sep.rstrip()
                    out.append(" " * (indent + cont))
                    before = len(out)
                    item.lines(indent + cont, out)
                    broken = len(out) > before
            out[-1] += closing


def atom(text):
    return Doc("atom", text)


class Renderer:
    def __init__(self, theory):
        self.generic = theory.generic
        self.type_of = TypeOf()
        self.annotate = ()
        self.genvars, self.tyvars = {}, {}

    def const_annotation_needed(self, name, args):
        generic = self.generic.get(name)
        if generic is None:
            return True
        wanted = type_vars(generic, set())
        if not wanted:
            return False
        have, ty = set(), generic
        for _ in args:
            if not is_fun(ty):
                break
            type_vars(ty[2][0], have)
            ty = ty[2][1]
        return not wanted <= have

    def const(self, tm, args, env):
        name = ("$" if tm[1] in env else "") + qname(tm[1])
        if tm[1] in self.annotate or self.const_annotation_needed(tm[1], args):
            name += ":" + render_type(tm[2], self.tyvars)
        return atom(name)

    def list_items(self, tm):
        items, elem = [], None
        while True:
            if tm[0] == "c" and tm[1] == "NIL" and items:
                return items if tm[2] == list_of(elem) else None
            if not (tm[0] == "a" and tm[1][0] == "a" and tm[1][1][0] == "c"):
                return None
            cons, x = tm[1][1], tm[1][2]
            if cons[1] != "CONS":
                return None
            a = self.type_of(x)
            if elem is None:
                elem = a
            if a != elem or cons[2] != fun(a, fun(list_of(a), list_of(a))):
                return None
            items.append(x)
            tm = tm[2]

    def term(self, tm, env):
        # env: rendered variable name -> types of the enclosing binders
        if tm[0] == "v":
            name = self.var_name(tm[1])
            text = qname(name, symbols=False)
            if env.get(name, [None])[-1] == tm[2]:
                return atom(text)
            return atom("{" + text + ":" + render_type(tm[2], self.tyvars) + "}")
        if tm[0] == "c":
            return self.const(tm, (), env)
        if tm[0] == "l" or self.binder(tm, env):
            return self.binding(tm, env)
        n = numeral(tm)
        if n is not None:
            return atom(f"#{n}")
        if tm[1] == ("c", "int_of_num", fun(NUM, INT)):
            n = numeral(tm[2])
            if n is not None:
                return atom(f"&{n}")
        data = byte_elements(tm)
        if data and None not in data:
            return Doc("bytes", items=tuple(atom(f"{b:02x}") for b in data))
        items = self.list_items(tm)
        if items is not None:
            docs = tuple(self.term(x, env) for x in items)
            return Doc("list", items=docs)
        args = []
        while tm[0] == "a":
            args.append(tm[2])
            tm = tm[1]
        args.reverse()
        head = self.const(tm, args, env) if tm[0] == "c" else self.term(tm, env)
        # (op a (op b c)) is printed as (op a b c); see CHAINS.
        while (
            tm[0] == "c"
            and tm[1] in CHAINS
            and tm[1] not in env
            and len(args) >= 2
            and self.plain(args[-1], tm[1], 2, env)
        ):
            args[-1:] = [args[-1][1][2], args[-1][2]]
        docs = (head,) + tuple(self.term(a, env) for a in args)
        return Doc("app", items=docs)

    def plain(self, tm, name, nargs, env):
        """Whether tm is the constant name applied to nargs arguments and
        printed without a type or $ mark."""
        args = []
        while tm[0] == "a" and len(args) < nargs:
            args.append(tm[2])
            tm = tm[1]
        return (
            len(args) == nargs
            and tm[0] == "c"
            and tm[1] == name
            and name not in env
            and not self.const_annotation_needed(name, args)
        )

    def binder(self, tm, env):
        """The binder constant if tm is (b (\\x. body)), printed (bx. body)."""
        if tm[0] == "a" and tm[2][0] == "l" and tm[1][0] == "c":
            if tm[1][1] in BINDERS and self.plain(tm, tm[1][1], 1, env):
                return tm[1][1]
        return None

    def binding(self, tm, env):
        """An abstraction or binder, with nested ones of the same kind:
        (\\x:a y:b. body) or (!x:a y:b. body)."""
        kind = "\\" if tm[0] == "l" else self.binder(tm, env)
        names, texts = [], []
        while True:
            if kind == "\\" and tm[0] == "l":
                v, tm = tm[1], tm[2]
            elif kind != "\\" and self.binder(tm, env) == kind:
                v, tm = tm[2][1], tm[2][2]
            else:
                break
            name = self.var_name(v[1])
            ty = render_type(v[2], self.tyvars)
            texts.append(qname(name, symbols=False) + ":" + ty)
            names.append(name)
            env.setdefault(name, []).append(v[2])
        body = self.term(tm, env)
        for name in names:
            env[name].pop()
            if not env[name]:
                del env[name]
        return Doc("abs", "(" + kind + " ".join(texts) + ".", (body,))

    def var_name(self, name):
        return self.genvars.get(name, name)

    def number_generated(self, tm):
        """Renumber generated names in order of first occurrence: variables
        called _<digits> (from genvar) become _1, _2, ..., and type
        variables called ?<digits> (invented by the parser) become ?1,
        ?2, .... HOL Light numbers both by global counters, so the same
        definition gets different names in different load orders. Each
        renaming is a bijection on its names and leaves all other names
        alone, so it preserves the structure of the term."""
        self.genvars, self.tyvars, stack = {}, {}, [tm]
        while stack:
            t = stack.pop()
            if t[0] in "al":
                stack.extend((t[2], t[1]))
                continue
            if GENVAR.match(t[1]) and t[0] == "v" and t[1] not in self.genvars:
                self.genvars[t[1]] = f"_{len(self.genvars) + 1}"
            types = [t[2]]
            while types:
                ty = types.pop()
                if ty[0] == "t":
                    types.extend(reversed(ty[2]))
                elif GENTYVAR.match(ty[1]) and ty[1] not in self.tyvars:
                    self.tyvars[ty[1]] = f"?{len(self.tyvars) + 1}"

    def theorem(self, th, annotate=()):
        """Render th, showing the types of the constants in annotate.

        A type definition's entry annotates its abs and rep constants:
        their types are the only place that shows the order of the new
        type's arguments."""
        if th[0]:
            raise Failed("theorem has hypotheses")
        self.annotate = annotate
        self.number_generated(th[1])
        out = ["|- "]
        self.term(th[1], {}).lines(3, out)
        return "\n".join(out)


# ----- accepted files
#
# An entry is a header line followed by its rendering, indented by two
# spaces, and a blank line. Lines starting with `#` are comments.


def stored(text):
    if len(text) <= LARGE:
        return text
    digest = hashlib.sha256(text.encode()).hexdigest()
    return f"{HASHED}{digest} ({len(text)} characters, not shown)"


def read_entries(path):
    entries = {}
    try:
        with open(path, encoding="utf-8") as f:
            lines = f.read().split("\n")
    except FileNotFoundError:
        return entries
    header, body = None, []
    for line in lines + [""]:
        if line.startswith("#") and header is None:
            continue
        if line.startswith("  ") and header is not None:
            body.append(line[2:])
        elif line == "":
            if header is not None:
                if header in entries:
                    raise Failed(f"{path}: duplicate entry {header}")
                entries[header] = "\n".join(body)
            header, body = None, []
        elif header is None:
            header = line
        else:
            raise Failed(f"{path}: malformed entry {header}")
    return entries


def rendered_bytes(text):
    """(name, bytes) if text renders a definition `|- (= name #x[..])`,
    else None. check-binary reads byte lists this way."""
    m = re.fullmatch(r"\|- \(= (\S+)\s+#x\[([0-9a-f\s]*)\]\)", text)
    if m is None:
        return None
    return m.group(1), bytes(int(b, 16) for b in m.group(2).split())


def byte_note(name, data):
    """The comment written before a byte-list definition."""
    return f"# {name}: {len(data)} bytes, sha256 {hashlib.sha256(data).hexdigest()}"


def write_entries(path, comment, entries, order=None):
    """Write entries in the given order of headers, or sorted. A byte-list
    definition is preceded by byte_note."""
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(comment)
        for header in order if order is not None else sorted(entries):
            text = entries[header]
            data = rendered_bytes(text)
            note = byte_note(*data) + "\n" if data else ""
            body = text.replace("\n", "\n  ")
            f.write(f"\n{note}{header}\n  {body}\n")


def read_metadata(path):
    """The `# key: value` lines at the top of a generated layer file."""
    out = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if not line.startswith("#"):
                break
            key, sep, value = line[1:].strip().partition(": ")
            if sep and key in ("pin", "source"):
                out.append((key, value))
    return out


def read_layers(paths):
    """The entries of the generated layer files: header -> (text, path).
    paths[0] is the HOL Light layer, the only one that may list axioms. A
    header may appear in only one layer."""
    out = {}
    for k, path in enumerate(paths):
        for header, text in read_entries(path).items():
            if header in out:
                raise Failed(
                    f"{header} is in both {short(out[header][1])} and {short(path)}"
                )
            if k and is_axiom(header):
                raise Failed(f"{short(path)} lists {header}; only HOL Light's may")
            out[header] = (text, path)
    return out


AXIOM = "axiom "


def axiom_header(text):
    """Axioms have no names; their entries are keyed by a hash."""
    return AXIOM + hashlib.sha256(text.encode()).hexdigest()[:16]


def is_axiom(header):
    return header.startswith(AXIOM)


def short(path):
    """accepted/... part of a path, for messages."""
    parts = os.path.normpath(path).split(os.sep)
    return (
        os.sep.join(parts[parts.index("accepted") :]) if "accepted" in parts else path
    )


LICENSE_COMMENT = """\
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
"""
# Every .defs file says where its notation is explained.
NOTATION_COMMENT = (
    "# The notation is explained in proofs/hol_light/hol_trace/accepted/README.md.\n"
)

DEFS_COMMENT = (
    LICENSE_COMMENT
    + """\
# {proof}
#
# The definitions that the main theorems use beyond the generated
# layers. Written by `hol-trace compare --accept`. check-binary
# compares the byte list with functions in binaries, through
# proofs/hol_light/bind.yml.
"""
    + NOTATION_COMMENT
)

THMS_COMMENT = (
    LICENSE_COMMENT
    + """\
# {proof}
#
# The main theorems. Written by `hol-trace compare --accept`. This
# is what the proof claims.
"""
)


# ----- byte lists


def byte_elements(tm):
    """For a literal list [x0; ...] of type (word 8) list, the list of
    bytes, with None for an element that is not `word n` with a
    canonical numeral n < 256. None if tm is not such a list."""
    out = []
    while tm != ("c", "NIL", list_of(BYTE)):
        if not (tm[0] == "a" and tm[1][0] == "a" and tm[1][1] == BYTE_CONS):
            return None
        x = tm[1][2]
        n = numeral(x[2]) if x[0] == "a" and x[1] == BYTE_WORD else None
        out.append(n if n is not None and n < 256 else None)
        tm = tm[2]
    return out


# ----- conformance


def conform(
    result_path,
    proof,
    theorem_names,
    layer_paths,
    defs_path,
    thms_path,
    accept=False,
    accept_hashed=False,
):
    """Check one replay result. Return a list of report lines.

    proof: the function's name; theorem_names: the proof's main theorems;
    layer_paths: the generated layer files
    (base and spec), HOL Light's first, never written here; defs_path, thms_path: the
    proof's own accepted files. With accept, rewrite the proof's files to
    hold exactly what the result needs beyond the layers, but only if
    nothing differs from a layer, and only if every new entry is shown in
    full or accept_hashed is set."""
    axioms, definitions, typedefs, named = read_result(result_path)
    theory = Theory(definitions, typedefs)
    render = Renderer(theory)

    names = [n for n, _ in named]
    if names != theorem_names:
        raise Failed("replay result has the wrong theorem list")
    for n, th in named:
        if th[0]:
            raise Failed(f"{n} has hypotheses")

    layers = read_layers(layer_paths)
    defs, thms = read_entries(defs_path), read_entries(thms_path)
    # A definition that a shared file now makes, for example after it moved
    # there from the proof, must leave the proof's file. --accept drops it;
    # its text is then checked against the shared file like any other.
    moved = [f"{h} is also in {short(layers[h][1])}" for h in defs if h in layers]
    if moved and not accept:
        raise Failed(f"{short(defs_path)}: " + "; ".join(moved))
    defs = {h: t for h, t in defs.items() if h not in layers}
    # The proof's files are rebuilt from what this result reaches.
    new_defs, new_thms = {}, {}
    layer_problems, problems, residue, hashed = [], [], [], []

    def check_entry(header, text, entries, new_entries):
        text = stored(text)
        if header in layers:
            if layers[header][0] != text:
                layer_problems.append(
                    f"{header} differs from {short(layers[header][1])}"
                )
            return
        if header not in entries:
            residue.append(header)
        elif entries[header] != text:
            problems.append(f"{header} differs from the accepted one")
        if entries.get(header) != text and text.startswith(HASHED):
            hashed.append(header)
        new_entries[header] = text

    for th in axioms:
        text = render.theorem(th)
        header = axiom_header(text)
        if header not in layers:
            # Never accept: only the HOL Light layer lists axioms.
            raise Failed(f"{header} is not an accepted axiom:\n{text}")
        check_entry(header, text, defs, new_defs)

    const_defs, type_defs = theory.closure([th for _, th in named] + axioms)
    for name, th in sorted(const_defs.items()):
        check_entry(f"definition {qname(name)}", render.theorem(th), defs, new_defs)
    for name, th in sorted(type_defs.items()):
        check_entry(
            f"typedef {qname(name)}",
            render.theorem(th, theory.typedef_consts[name]),
            defs,
            new_defs,
        )
    prefix = f"theorem {proof} "
    for name, th in named:
        text = render.theorem(th)
        if len(text) > LARGE:
            # Never accept: a main theorem must be readable.
            raise Failed(f"{name} is too large to store for review")
        check_entry(prefix + name, text, thms, new_thms)
    unused = [h for h in defs if h not in new_defs]
    unused += [h for h in thms if h not in new_thms]
    problems += [f"{h} is no longer used" for h in unused]

    report = [
        f"{len(const_defs)} definitions, {len(type_defs)} type definitions, "
        f"{len(named)} theorems"
    ]
    if layer_problems:
        # Never accept: the layers are only written by `hol-trace layers`.
        raise Failed(
            "; ".join(layer_problems) + ". If the pinned libraries or the "
            "specifications changed, regenerate the layers with "
            "`scripts/autogen --hol-trace-defs`"
        )
    if accept and hashed and not accept_hashed:
        raise Failed(
            "these entries would be accepted as hashes, without a rendering "
            "to review: " + "; ".join(hashed) + ". Check where they come "
            "from, then use --accept-hashed"
        )
    if accept:
        comment = DEFS_COMMENT.format(proof=proof)
        write_entries(defs_path, comment, new_defs)
        write_entries(thms_path, THMS_COMMENT.format(proof=proof), new_thms)
        report.extend(f"removed: {m}" for m in moved)
        report.extend(f"accepted: {p}" for p in problems + residue)
        return report
    if problems or residue:
        raise Failed("; ".join(problems + [f"not accepted: {r}" for r in residue]))
    return report
