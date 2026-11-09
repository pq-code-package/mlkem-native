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
        self.display = self.temporaries()
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

    def temporaries(self):
        """Display names for define_type's temporary constants.

        define_type first defines each constructor under a fresh name
        _<n> from genvar, HOL Light's global counter, and then the
        constructor C itself by |- C = _<n>. The counter depends on how
        many fresh names earlier proofs used, so _<n> is shown as _<C>
        instead. This applies only where exactly one definition has the
        form |- C = _<n>, with C alphanumeric; other constants keep their
        names. The renaming is injective: each C is defined once, and so
        names at most one constant. A constant whose own name is _<C>
        prints in quotes, so the two cannot be confused. _0, the numeral
        zero, is not a temporary."""
        aliases = {}
        for name, th in self.const_def.items():
            rhs = dest_eq(th[1])[1]
            if (
                rhs[0] == "c"
                and GENVAR.match(rhs[1])
                and rhs[1] != "_0"
                and rhs[1] in self.const_def
                and RAW_ALNUM.match(name)
            ):
                aliases.setdefault(rhs[1], []).append(name)
        return {t: f"_<{cs[0]}>" for t, cs in aliases.items() if len(cs) == 1}

    def const_name(self, name):
        """A constant's name in entry headers; see temporaries."""
        return self.display.get(name) or header_name(name)

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
# Kernel objects are printed in a notation close to HOL Light's own, but
# one in which every object has exactly one text and every text at most
# one object (up to the renumbering of generated names, below):
#
#   f a b              application of f to a and b; arguments that are not
#                      atoms are parenthesized
#   \x:ty y:ty. body   abstraction; also !, ?, ?!, @ for the binder constants
#                      applied to an abstraction. A binder, an infix
#                      expression or a `let` is parenthesized wherever it is
#                      not a whole term, a binder body or an operand of
#                      lower precedence
#   let x:ty = v in b  LET (\x. LET_END b) v; with several bindings,
#                      let x:ty = v and y:ty = w in b for
#                      LET (\x y. LET_END b) v w
#   a OP b             an infix operator; see INFIX for the operators, their
#                      precedence and associativity, and the exact types at
#                      which overloaded symbols such as <= stand for the
#                      num or the int constant
#   (a == b) r         == a b r, a congruence such as (a == b) (mod n)
#   abs x, mod n       int_abs x and int_mod n, at their int types
#   -x                 int_neg x; binds tighter than * and looser than
#                      DIV, MOD, div, rem, EXP, pow, o and :>
#   specification "c" f:ty. body
#                      (@f. !g. body[f g / f]) (99, ...), the form in
#                      which new_specification defines c: the tuple holds
#                      the character codes of "c", g is a genvar, and f
#                      occurs only applied to g; see Renderer.specification
#   x                  the variable bound by the innermost binder named x
#   {x:ty}             any other variable: a free one, or one whose
#                      binder is hidden by an inner binder of the same
#                      name and another type
#   c                  a constant whose type follows from its generic type
#                      and its arguments
#   (c args : ty)      a constant applied to args, the application of type
#                      ty; with no args, the constant has type ty
#   (op)               an operator symbol or keyword used as a constant
#                      without its notation, e.g. (/\) or (abs)
#   $c                 a constant whose name is bound by an enclosing binder
#   _1, _2, ...        variables named _<digits> (HOL Light's genvars),
#                      renumbered in order of first occurrence
#   "GEN%PVAR%1"       variables of set comprehensions (invented by the
#                      parser), renumbered likewise
#   _<C>               define_type's temporary constant _<n> for the
#                      constructor C; see Theory.temporaries
#   12, &12            a canonical numeral, and int_of_num of one
#   [a; b]             CONS a (CONS b NIL)
#   #x[0a ff]          [word 10; word 255] : byte list, every element
#                      `word n` with a canonical numeral n < 256
#
# and types:
#
#   'A, '?1            a type variable; ?<digits> renumbered like genvars
#   a -> b, a # b      function and product types, both right-nested;
#                      # binds tighter than ->
#   num list           a type constructor after its argument; with several,
#                      (a, b) name
#   64                 a numeral type tybit0 (... 1)
#   byte, int16, ...   word 8, word 16, word 32, word 64, word 128
#
# Names are printed raw if they are alphanumeric and no keyword, or
# symbolic, and as JSON strings otherwise: a variable named + or abs is
# "+" or "abs" wherever it appears, and so is a name that starts with a
# digit. A type constant named like an abbreviation, only of digits, or
# with a symbolic name, is quoted too. Equal text therefore implies equal kernel objects, up to
# the renumbering of generated names: a reviewer who reads the text reads
# exactly the object that is compared. Every subterm's type follows from
# its text, which is what lets the overloaded symbols name one constant.

RAW_ALNUM = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
RAW_SYMBOL = re.compile(r"[!#%&*+,\-/<=>?@\\^|~:]+\Z")
GENVAR = re.compile(r"_[0-9]+\Z")
GENTYVAR = re.compile(r"\?[0-9]+\Z")
# Variables that the parser invents for set comprehensions {x | P x}.
GENPVAR = re.compile(r"GEN%PVAR%[0-9]+\Z")
# Lines of the accepted files are at most 100 characters wide where
# breaking allows; write_entries indents each rendering by two.
WIDTH = 100 - 2
APP = 100  # precedence of application; atoms are APP + 1
# Binder constants, applied to an abstraction, are printed !x:ty. body.
BINDERS = {"!", "?", "?!", "@"}
BOOL2 = fun(BOOL, fun(BOOL, BOOL))
NUM2B, NUM2 = fun(NUM, fun(NUM, BOOL)), fun(NUM, fun(NUM, NUM))
INT2B, INT2 = fun(INT, fun(INT, BOOL)), fun(INT, fun(INT, INT))
# constant -> (exact type or None for any type, symbol, precedence,
# associativity). A constant is printed infix only at that type, with two
# arguments and no type annotation needed. Symbols shared by a num and an
# int constant are told apart by the type of their operands.
INFIX = {
    "==>": (BOOL2, "==>", 4, "r"),
    "\\/": (BOOL2, "\\/", 6, "r"),
    "/\\": (BOOL2, "/\\", 8, "r"),
    "=": (None, "=", 12, "n"),
    "<": (NUM2B, "<", 12, "n"),
    "<=": (NUM2B, "<=", 12, "n"),
    ">": (NUM2B, ">", 12, "n"),
    ">=": (NUM2B, ">=", 12, "n"),
    "int_lt": (INT2B, "<", 12, "n"),
    "int_le": (INT2B, "<=", 12, "n"),
    "int_gt": (INT2B, ">", 12, "n"),
    "int_ge": (INT2B, ">=", 12, "n"),
    ",,": (None, ",,", 13, "r"),
    ",": (None, ",", 14, "r"),
    "..": (fun(NUM, fun(NUM, fun(NUM, BOOL))), "..", 15, "r"),
    "+": (NUM2, "+", 16, "r"),
    "int_add": (INT2, "+", 16, "r"),
    "-": (NUM2, "-", 18, "l"),
    "int_sub": (INT2, "-", 18, "l"),
    "*": (NUM2, "*", 20, "r"),
    "int_mul": (INT2, "*", 20, "r"),
    "DIV": (NUM2, "DIV", 22, "l"),
    "MOD": (NUM2, "MOD", 22, "l"),
    "div": (INT2, "div", 22, "l"),
    "rem": (INT2, "rem", 22, "l"),
    "EXP": (NUM2, "EXP", 24, "n"),
    "int_pow": (fun(INT, fun(NUM, INT)), "pow", 24, "n"),
    "o": (None, "o", 26, "r"),
    ":>": (None, ":>", 30, "r"),
}
# int_neg x is printed -x, with this precedence.
NEG, NEG_PREC = ("c", "int_neg", fun(INT, INT)), 21
# constant -> (exact type, name printed in its place)
PREFIX = {
    "int_abs": (fun(INT, INT), "abs"),
    "int_mod": (fun(INT, fun(INT, fun(INT, BOOL))), "mod"),
}
# Words with a meaning in this notation. A variable or constant with such
# a name is quoted; an operator constant used without its notation is
# printed (op).
KEYWORDS = {
    "let",
    "and",
    "in",
    "o",
    "EXP",
    "pow",
    "abs",
    "mod",
    "DIV",
    "MOD",
    "div",
    "rem",
    "specification",
}
OPERATORS = (
    {sym for _, sym, _, _ in INFIX.values()}
    | set(INFIX)
    | {name for _, name in PREFIX.values()}
    | BINDERS
    | {"==", "\\", "->", "#", "|-", "&", ":"}
)
TYPE_ABBREV = {8: "byte", 16: "int16", 32: "int32", 64: "int64", 128: "int128"}


def header_name(name):
    """name as written in an entry's header: raw if alphanumeric or
    symbolic, else as a JSON string. Headers are keys, not terms."""
    if re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_']*|[!#%&*+,\-/<=>?@\\^|~]+", name) and (
        name not in {"\\", "->", "#", "|-"}
    ):
        return name
    return json.dumps(name)


def qname(name, symbols=True):
    """name as printed: raw if alphanumeric and no keyword, or, with
    symbols, symbolic; else as a JSON string."""
    if name not in KEYWORDS and (
        RAW_ALNUM.match(name) or (symbols and RAW_SYMBOL.match(name))
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


def type_name(name):
    if name == "1":  # the numeral type 1 is the type constant 1
        return name
    if name in TYPE_ABBREV.values() or name.isdigit():
        return json.dumps(name)
    # A symbolic type name such as # or -> would read as notation.
    return qname(name, symbols=False)


def type_doc(ty, tyvars={}, atomic=False):
    """The layout of ty; with atomic, parenthesized unless it is an atom.
    tyvars renames type variables; see Renderer.number_generated."""
    if ty[0] == "v":
        name = tyvars.get(ty[1], ty[1])
        return atom(
            "'" + (name if GENTYVAR.match(name) else qname(name, symbols=False))
        )
    n = finty(ty)
    if n is not None:
        return atom(str(n))
    if ty[1] == "word" and len(ty[2]) == 1 and finty(ty[2][0]) in TYPE_ABBREV:
        return atom(TYPE_ABBREV[finty(ty[2][0])])
    if not ty[2]:
        return atom(type_name(ty[1]))
    if is_fun(ty) or is_prod(ty):
        test, op = (is_fun, "->") if is_fun(ty) else (is_prod, "#")
        parts = []
        while test(ty):
            parts.append(ty[2][0])
            ty = ty[2][1]
        parts.append(ty)
        # Operands are atoms, constructor applications or parenthesized;
        # an operand of -> may also be a product, since # binds tighter.
        docs = [
            type_doc(
                p,
                tyvars,
                atomic=(is_fun(p) or is_prod(p)) and not (op == "->" and is_prod(p)),
            )
            for p in parts
        ]
        doc = Doc("fill", ("", f" {op} ", "", 4), tuple(docs))
    elif len(ty[2]) == 1:
        doc = Doc(
            "seq",
            items=(type_doc(ty[2][0], tyvars, atomic=True), atom(type_name(ty[1]))),
        )
    else:
        args = tuple(type_doc(a, tyvars) for a in ty[2])
        doc = Doc(
            "seq", items=(Doc("fill", ("(", ", ", ")"), args), atom(type_name(ty[1])))
        )
    return Doc("paren", items=(doc,)) if atomic else doc


def render_type(ty, tyvars={}, atomic=False):
    """ty as printed on one line."""
    parts = []
    type_doc(ty, tyvars, atomic).flat(parts)
    return "".join(parts)


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


def app_of(f, x):
    return ("a", f, x)


def tag_name(tm):
    """The name whose character codes the right-nested tuple tm holds, as
    new_specification builds it, or None. Only printable ASCII."""
    codes = []
    while (
        tm[0] == "a" and tm[1][0] == "a" and tm[1][1][0] == "c" and tm[1][1][1] == ","
    ):
        n = numeral(tm[1][2])
        if n is None:
            return None
        codes.append(n)
        tm = tm[2]
    n = numeral(tm)
    if n is None:
        return None
    codes.append(n)
    if not all(32 <= n < 127 for n in codes):
        return None
    return "".join(map(chr, codes))


def drop_tag(tm, f, g):
    """(tm with every f g replaced by a variable f of the type of f g,
    the number of replacements), or None if f or g occur otherwise,
    another variable has either name, or a binder rebinds one."""
    stack, out, uses = [(tm, False)], [], 0
    names = (f[1], g[1])
    while stack:
        t, done = stack.pop()
        if done:
            right, left = out.pop(), out.pop()
            out.append(("a", left, right) if t[0] == "a" else ("l", left, right))
            continue
        if t == ("a", f, g):
            out.append(("v", f[1], f[2][2][1]))
            uses += 1
        elif t[0] == "v":
            if t[1] in names:
                return None
            out.append(t)
        elif t[0] == "c":
            out.append(t)
        elif t[0] == "l":
            if t[1][1] in names:
                return None
            stack.append((t, True))
            stack.append((t[2], False))
            out.append(t[1])
        else:
            stack.append((t, True))
            stack.append((t[2], False))
            stack.append((t[1], False))
    return out[0], uses


class Doc:
    """A layout unit, with its width when printed on one line:

    atom   text
    seq    items separated by spaces; broken, every item after the first
           on a new line, indented by 2
    chain  first, then (op, item) pairs; broken, each pair on a new line
    bind   a binder head (a fill of its variables) and its body; broken,
           the body on a new line, indented by 2
    let    `let v = x and ... in` and the body; broken, each binding on
           its own line, the body on a new line
    paren  an item in parentheses
    join   items without separators, e.g. a variable and its type
    fill   opening, items separated by sep, closing; broken, as many items
           on each line as fit, continued below the first item or, with a
           fourth text element n, indented by n (used for long types)
    """

    __slots__ = ("kind", "text", "items", "width")

    def __init__(self, kind, text="", items=()):
        self.kind, self.text, self.items = kind, text, items
        if kind == "atom":
            self.width = len(text)
        elif kind == "seq":
            self.width = sum(i.width for i in items) + len(items) - 1
        elif kind == "chain":
            self.width = items[0].width + sum(
                len(self.op_text(op)) + i.width for op, i in items[1:]
            )
        elif kind == "bind":
            self.width = items[0].width + 1 + items[1].width
        elif kind == "let":
            # let h v and h v in body
            pairs = items[:-1]
            self.width = (
                sum(h.width + 1 + v.width for h, v in pairs)
                + 4
                + 5 * (len(pairs) - 1)
                + 4
                + items[-1].width
            )
        elif kind == "paren":
            self.width = items[0].width + 2
        elif kind == "join":
            self.width = sum(i.width for i in items)
        else:  # fill: text = (opening, sep, closing[, indent])
            opening, sep, closing = text[:3]
            self.width = (
                len(opening)
                + sum(i.width for i in items)
                + len(sep) * (len(items) - 1)
                + len(closing)
            )

    @staticmethod
    def op_text(op):
        return {",": ", ", "..": ".."}.get(op, f" {op} ")

    def flat(self, out):
        k = self.kind
        if k == "atom":
            out.append(self.text)
        elif k == "seq":
            for n, item in enumerate(self.items):
                if n:
                    out.append(" ")
                item.flat(out)
        elif k == "chain":
            self.items[0].flat(out)
            for op, item in self.items[1:]:
                out.append(self.op_text(op))
                item.flat(out)
        elif k == "bind":
            self.items[0].flat(out)
            out.append(" ")
            self.items[1].flat(out)
        elif k == "join":
            for item in self.items:
                item.flat(out)
        elif k == "let":
            for n, (head, value) in enumerate(self.items[:-1]):
                out.append("let " if n == 0 else " and ")
                head.flat(out)
                out.append(" ")
                value.flat(out)
            out.append(" in ")
            self.items[-1].flat(out)
        elif k == "paren":
            out.append("(")
            self.items[0].flat(out)
            out.append(")")
        else:
            opening, sep, closing = self.text[:3]
            out.append(opening)
            for n, item in enumerate(self.items):
                if n:
                    out.append(sep)
                item.flat(out)
            out.append(closing)

    def lines(self, indent, out, tail=0):
        """Append to out, a list of lines; the first continues out[-1].
        Continuation lines are indented relative to indent; tail is the
        width of what follows on the last line, such as closing
        parentheses. Layout only places line breaks between tokens: it
        does not change the text's meaning."""
        if self.kind == "atom" or len(out[-1]) + self.width + tail <= WIDTH:
            parts = []
            self.flat(parts)
            out[-1] += "".join(parts)
            return
        k = self.kind
        if k == "seq":
            last = len(self.items) - 1
            self.items[0].lines(indent, out, tail if last == 0 else 0)
            broken = False
            for n, item in enumerate(self.items[1:], 1):
                after = tail if n == last else 0
                fits = len(out[-1]) + 1 + item.width + after <= WIDTH
                # A last argument that does not fit continues the line,
                # so that f (g (h ...)) does not indent once per level.
                hang = n == last and len(out[-1]) < WIDTH // 2
                if not broken and (fits or hang):
                    out[-1] += " "
                    item.lines(indent if hang and not fits else indent + 2, out, after)
                else:
                    out.append(" " * (indent + 2))
                    broken = True
                    item.lines(indent + 2, out, after)
        elif k == "chain":
            last = len(self.items) - 1
            self.items[0].lines(indent, out)
            for n, (op, item) in enumerate(self.items[1:], 1):
                lead = op + " "
                out.append(" " * indent + lead)
                item.lines(indent + len(lead), out, tail if n == last else 0)
        elif k == "bind":
            self.items[0].lines(indent, out)
            out.append(" " * (indent + 2))
            self.items[1].lines(indent + 2, out, tail)
        elif k == "join":
            rest = [i.width for i in self.items]
            for n, item in enumerate(self.items):
                item.lines(indent, out, tail + sum(rest[n + 1 :]))
        elif k == "let":
            for n, (head, value) in enumerate(self.items[:-1]):
                if n:
                    out.append(" " * indent + "and ")
                else:
                    out[-1] += "let "
                head.lines(indent + 4, out)
                # " in" follows the last value.
                after = 3 if n == len(self.items) - 2 else 0
                if len(out[-1]) + 1 + value.width + after <= WIDTH:
                    out[-1] += " "
                else:
                    out.append(" " * (indent + 4))
                value.lines(indent + 4, out, after)
            out[-1] += " in"
            out.append(" " * indent)
            self.items[-1].lines(indent, out, tail)
        elif k == "paren":
            out[-1] += "("
            self.items[0].lines(indent, out, tail + 1)
            out[-1] += ")"
        else:
            opening, sep, closing = self.text[:3]
            cont = len(out[-1]) + len(opening)
            if len(self.text) > 3:
                cont = indent + self.text[3]
            out[-1] += opening
            last = len(self.items) - 1
            self.items[0].lines(
                cont, out, tail + len(closing) if last == 0 else len(sep.rstrip())
            )
            for n, item in enumerate(self.items[1:], 1):
                after = tail + len(closing) if n == last else len(sep.rstrip())
                if len(out[-1]) + len(sep) + item.width + after <= WIDTH:
                    out[-1] += sep
                    item.lines(len(out[-1]), out, after)
                else:
                    out[-1] += sep.rstrip()
                    out.append(" " * cont)
                    item.lines(cont, out, after)
            out[-1] += closing


def atom(text):
    return Doc("atom", text)


class Renderer:
    def __init__(self, theory):
        self.generic = theory.generic
        self.display = theory.display
        self.type_of = TypeOf()
        self.annotate = ()
        self.genvars, self.tyvars, self.name_counts = {}, {}, {}

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

    def ty(self, ty, atomic=False):
        return type_doc(ty, self.tyvars, atomic)

    def typed(self, name, ty):
        """(name : ty), a constant at its type."""
        return Doc("paren", items=(Doc("seq", items=(atom(name), self.ascribed(ty))),))

    def ascribed(self, ty):
        """`: ty`, kept on one line with its type's first part."""
        return Doc("join", items=(atom(": "), self.ty(ty)))

    def const_name(self, name, env):
        if name in self.display:
            # _<C> is never the printed name of a variable.
            return self.display[name]
        if name in OPERATORS or name in KEYWORDS:
            text = (
                f"({name})"
                if RAW_SYMBOL.match(name) or name in KEYWORDS or name == ".."
                else qname(name)
            )
        else:
            text = qname(name)
        return ("$" if name in env else "") + text

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

    def spine(self, tm):
        args = []
        while tm[0] == "a":
            args.append(tm[2])
            tm = tm[1]
        args.reverse()
        return tm, args

    def notation(self, head, args, env):
        """(symbol, precedence, associativity) if head applied to args is
        printed infix, else None."""
        if head[0] != "c" or head[1] in env or len(args) != 2:
            return None
        entry = INFIX.get(head[1])
        if entry is None or (entry[0] is not None and head[2] != entry[0]):
            return None
        if head[1] in self.annotate or self.const_annotation_needed(head[1], args):
            return None
        return entry[1:]

    def term(self, tm, env, ctx=0):
        """The layout of tm, parenthesized if its precedence is below ctx.
        env: printed variable name -> types of the enclosing binders."""
        doc, prec = self.build(tm, env)
        return Doc("paren", items=(doc,)) if prec < ctx else doc

    def build(self, tm, env):
        if tm[0] == "v":
            name = self.var_name(tm[1])
            text = qname(name, symbols=False)
            if env.get(name, [None])[-1] == tm[2]:
                return atom(text), APP + 1
            return Doc(
                "join", items=(atom("{" + text + ":"), self.ty(tm[2]), atom("}"))
            ), APP + 1
        if tm[0] == "c":
            name = self.const_name(tm[1], env)
            if tm[1] in self.annotate or self.const_annotation_needed(tm[1], ()):
                return self.typed(name, tm[2]), APP + 1
            return atom(name), APP + 1
        if tm[0] == "l" or self.binder(tm, env):
            return self.binding(tm, env), 0
        n = numeral(tm)
        if n is not None:
            return atom(str(n)), APP + 1
        if tm[1] == ("c", "int_of_num", fun(NUM, INT)):
            n = numeral(tm[2])
            if n is not None:
                return atom(f"&{n}"), APP + 1
        data = byte_elements(tm)
        if data and None not in data:
            items = tuple(atom(f"{b:02x}") for b in data)
            return Doc("fill", ("#x[", " ", "]"), items), APP + 1
        items = self.list_items(tm)
        if items is not None:
            docs = tuple(self.term(x, env, 1) for x in items)
            return Doc("fill", ("[", "; ", "]"), docs), APP + 1
        let = self.let(tm, env)
        if let:
            return let, 0
        spec = self.specification(tm, env)
        if spec:
            return spec, 0
        head, args = self.spine(tm)
        if (
            head[0] == "c"
            and head[1] == "=="
            and "==" not in env
            and len(args) == 3
            and not self.const_annotation_needed("==", args)
        ):
            # (a == b) r
            pair = Doc(
                "chain",
                items=(
                    self.term(args[0], env, APP),
                    ("==", self.term(args[1], env, APP)),
                ),
            )
            rel = self.term(args[2], env, APP + 1)
            return Doc("seq", items=(Doc("paren", items=(pair,)), rel)), APP
        infix = self.notation(head, args, env)
        if infix:
            return self.chain(head, args, env, *infix)
        if (
            head == NEG
            and len(args) == 1
            and NEG[1] not in env
            and NEG[1] not in self.annotate
        ):
            return self.negation(args[0], env), NEG_PREC
        if len(args) > 1 and self.binder(app_of(head, args[0]), env):
            # (@x. body) y: a binder applied to further arguments.
            docs = (self.term(app_of(head, args[0]), env, APP + 1),)
            docs += tuple(self.term(a, env, APP + 1) for a in args[1:])
            return Doc("seq", items=docs), APP
        if head[0] == "c":
            name = self.const_name(head[1], env)
            alias = PREFIX.get(head[1])
            if alias and head[2] == alias[0] and head[1] not in env:
                hdoc, annotated = atom(alias[1]), False
            elif head[1] in self.annotate:
                hdoc, annotated = self.typed(name, head[2]), False
            else:
                hdoc = atom(name)
                annotated = self.const_annotation_needed(head[1], args)
            docs = (hdoc,) + tuple(self.term(a, env, APP + 1) for a in args)
            if annotated:
                # (c args : ty), the type of the whole application.
                docs += (self.ascribed(self.type_of(tm)),)
                return Doc("paren", items=(Doc("seq", items=docs),)), APP + 1
            return Doc("seq", items=docs), APP
        docs = (self.term(head, env, APP + 1),) + tuple(
            self.term(a, env, APP + 1) for a in args
        )
        return Doc("seq", items=docs), APP

    def negation(self, x, env):
        """-x. An operand that is not an atom is parenthesized, and so is a
        symbolic constant, so that -x never reads as one name."""
        doc = self.term(x, env, APP + 1)
        if (
            doc.kind == "atom"
            and RAW_SYMBOL.match(doc.text[0])
            and not re.match(r"&[0-9]", doc.text)
        ):
            doc = Doc("paren", items=(doc,))
        return Doc("join", items=(atom("-"), doc))

    def specification(self, tm, env):
        """specification "c" f:ty. body, for

            (@f:tag -> ty. !g:tag. body[f g / f]) (99, ...)

        the form in which new_specification defines the constant c: the
        tag is the tuple of c's character codes, right-nested, and makes
        constants with equivalent specifications differ. Printed so only
        if g is a genvar that occurs nowhere else, and f occurs only
        applied to g, and no binder in body rebinds either name. The text
        then determines the term: the tag and its type follow from "c",
        and g, a genvar bound right after f, is renumbered the same in
        every term that prints alike."""
        if not (tm[0] == "a" and tm[1][0] == "a" and tm[1][2][0] == "l"):
            return None
        eps, (_, f, body), tag = tm[1][1], tm[1][2], tm[2]
        if eps[0] != "c" or eps[1] != "@" or "@" in env or "@" in self.annotate:
            return None
        name = tag_name(tag)
        tag_ty = self.type_of(tag)
        if name is None or not is_fun(f[2]) or f[2][2][0] != tag_ty:
            return None
        if not (
            body[0] == "a"
            and body[1] == ("c", "!", fun(fun(tag_ty, BOOL), BOOL))
            and body[2][0] == "l"
            and "!" not in env
            and "!" not in self.annotate
        ):
            return None
        g, inner = body[2][1], body[2][2]
        if g[2] != tag_ty or not GENVAR.match(g[1]) or f[1] == g[1]:
            return None
        dropped = drop_tag(inner, f, g)
        if dropped is None:
            return None
        inner, uses = dropped
        # g's name occurs only in its binder and in the uses dropped here,
        # so leaving it out loses nothing that the renumbering keeps.
        if self.name_counts.get(g[1], 0) != 1 + uses:
            return None
        ty = f[2][2][1]
        fname = self.var_name(f[1])
        env.setdefault(fname, []).append(ty)
        doc = self.term(inner, env)
        env[fname].pop()
        if not env[fname]:
            del env[fname]
        bound = Doc(
            "join",
            items=(
                atom(qname(fname, symbols=False) + ":"),
                self.ty(ty, atomic=True),
                atom("."),
            ),
        )
        head = Doc("seq", items=(atom(f"specification {json.dumps(name)}"), bound))
        return Doc("bind", items=(head, doc))

    def chain(self, head, args, env, sym, prec, assoc):
        """a OP b, with right-nested operands of the same constant of a
        right-associative operator in one chain."""
        left = prec + (1 if assoc != "l" else 0)
        right = prec + (1 if assoc != "r" else 0)
        if sym == "..":
            # Written without spaces, so an infix operand would read as
            # binding looser: (n - 1)..m, not n - 1..m.
            left = right = APP
        items = [self.term(args[0], env, left)]
        x = args[1]
        while assoc == "r":
            h, a = self.spine(x)
            if h != head or self.notation(h, a, env) is None:
                break
            items.append((sym, self.term(a[0], env, left)))
            x = a[1]
        items.append((sym, self.term(x, env, right)))
        return Doc("chain", items=tuple(items)), prec

    def binder(self, tm, env):
        """The binder constant if tm is (b (\\x. body)), printed bx. body."""
        if tm[0] == "a" and tm[2][0] == "l" and tm[1][0] == "c":
            b = tm[1][1]
            if (
                b in BINDERS
                and b not in env
                and b not in self.annotate
                and not self.const_annotation_needed(b, (tm[2],))
            ):
                return b
        return None

    def binding(self, tm, env):
        """An abstraction or binder, with nested ones of the same kind:
        \\x:a y:b. body or !x:a y:b. body."""
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
            texts.append(
                Doc(
                    "join",
                    items=(
                        atom(qname(name, symbols=False) + ":"),
                        self.ty(v[2], atomic=True),
                    ),
                )
            )
            names.append(name)
            env.setdefault(name, []).append(v[2])
        body = self.term(tm, env)
        for name in names:
            env[name].pop()
            if not env[name]:
                del env[name]
        head = Doc("fill", (kind, " ", "."), tuple(texts))
        return Doc("bind", items=(head, body))

    def let(self, tm, env):
        """let x:ty = v and ... in body, for LET (\\x. ... LET_END body) v ...,
        as HOL Light parses it."""
        head, args = self.spine(tm)
        if head[0] != "c" or head[1] != "LET" or "LET" in env or len(args) < 2:
            return None
        f, values = args[0], args[1:]
        bound = []
        for _ in values:
            if f[0] != "l":
                return None
            bound.append(f[1])
            f = f[2]
        end, end_args = self.spine(f)
        if end[0] != "c" or end[1] != "LET_END" or len(end_args) != 1:
            return None
        if "LET_END" in env or self.const_annotation_needed("LET", args):
            return None
        if self.const_annotation_needed("LET_END", end_args):
            return None
        # The values are outside the scope of the bound variables.
        items = []
        for v, value in zip(bound, values):
            name = self.var_name(v[1])
            text = Doc(
                "join",
                items=(
                    atom(qname(name, symbols=False) + ":"),
                    self.ty(v[2], atomic=True),
                    atom(" ="),
                ),
            )
            items.append((text, self.term(value, env)))
        names = [self.var_name(v[1]) for v in bound]
        for name, v in zip(names, bound):
            env.setdefault(name, []).append(v[2])
        body = self.term(end_args[0], env)
        for name in names:
            env[name].pop()
            if not env[name]:
                del env[name]
        return Doc("let", items=tuple(items) + (body,))

    def var_name(self, name):
        return self.genvars.get(name, name)

    def number_generated(self, tm):
        """Renumber generated names in order of first occurrence: variables
        called _<digits> (from genvar) become _1, _2, ..., variables called
        GEN%PVAR%<digits> (invented by the parser for set comprehensions)
        become GEN%PVAR%1, ..., and type variables called ?<digits>
        (invented by the parser) become ?1, ?2, .... HOL Light numbers
        them by global counters, so the same definition gets different
        names in different load orders, or when proofs are skipped. Each
        renaming is a bijection on its names and leaves all other names
        alone, so it preserves the structure of the term."""
        self.genvars, self.tyvars, stack = {}, {}, [tm]
        self.name_counts = {}
        counts = {"_": 0, "GEN%PVAR%": 0}
        while stack:
            t = stack.pop()
            if t[0] in "al":
                stack.extend((t[2], t[1]))
                continue
            if t[0] == "v":
                self.name_counts[t[1]] = self.name_counts.get(t[1], 0) + 1
            if t[0] == "v" and t[1] not in self.genvars:
                for prefix, pattern in (("_", GENVAR), ("GEN%PVAR%", GENPVAR)):
                    if pattern.match(t[1]):
                        counts[prefix] += 1
                        self.genvars[t[1]] = f"{prefix}{counts[prefix]}"
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
    """(name, bytes) if text renders a definition `|- name = #x[..]`,
    else None. check-binary reads byte lists this way."""
    m = re.fullmatch(r"\|- (\S+)\s+= #x\[([0-9a-f\s]*)\]", text)
    if m is None:
        return None
    return m.group(1), bytes(int(b, 16) for b in m.group(2).split())


def byte_note(name, data):
    """The two comment lines written before a byte-list definition."""
    digest = hashlib.sha256(data).hexdigest()
    return f"# {name}: {len(data)} bytes\n# sha256 {digest}"


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
# The definitions that the main theorems use beyond the shared files
# in accepted/base and accepted/spec. Written by `hol-trace outline`
# or `hol-trace compare --accept`. check-binary compares the byte list
# with functions in binaries, through proofs/hol_light/bind.yml.
"""
    + NOTATION_COMMENT
)

THMS_COMMENT = (
    LICENSE_COMMENT
    + """\
# {proof}
#
# The main theorems. Written by `hol-trace outline` or `hol-trace
# compare --accept`. This is what the proof claims.
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
        check_entry(
            f"definition {theory.const_name(name)}", render.theorem(th), defs, new_defs
        )
    for name, th in sorted(type_defs.items()):
        check_entry(
            f"typedef {header_name(name)}",
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
        # Never accept: the layers are only written by `hol-trace outline`.
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
