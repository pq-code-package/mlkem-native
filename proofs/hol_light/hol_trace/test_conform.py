# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Tests for conform.py. Run: python3 -m unittest test_conform"""

import os
import tempfile
import unittest

import conform as c

A, B = ("v", "A"), ("v", "B")
BOOL, NUM, INT = c.BOOL, c.NUM, c.INT
fun, list_of = c.fun, c.list_of


def prod(a, b):
    return ("t", "prod", (a, b))


def var(n, ty):
    return ("v", n, ty)


def const(n, ty):
    return ("c", n, ty)


def app(f, *xs):
    for x in xs:
        f = ("a", f, x)
    return f


def lam(v, b):
    return ("l", v, b)


def eq(x, y, ty=NUM):
    return app(const("=", fun(ty, fun(ty, BOOL))), x, y)


def num(n):
    bits = const("_0", NUM)
    for b in bin(n)[2:] if n else "":
        bits = app(const("BIT1" if b == "1" else "BIT0", fun(NUM, NUM)), bits)
    return app(const("NUMERAL", fun(NUM, NUM)), bits)


def enc_type(ty):
    if ty[0] == "v":
        return b"v%d:%s" % (len(ty[1]), ty[1].encode())
    out = b"t%d:%s%d:" % (len(ty[1]), ty[1].encode(), len(ty[2]))
    return out + b"".join(enc_type(a) for a in ty[2])


def enc_term(tm):
    if tm[0] in "vc":
        return (
            tm[0].encode() + b"%d:%s" % (len(tm[1]), tm[1].encode()) + enc_type(tm[2])
        )
    return tm[0].encode() + enc_term(tm[1]) + enc_term(tm[2])


def enc_thm(concl):
    return b"h0:" + enc_term(concl)


def result(axioms=(), defs=(), typedefs=(), named=()):
    out = c.RESULT_MAGIC
    out += b"".join(b"X" + enc_thm(t) for t in axioms)
    out += b"".join(b"D" + enc_thm(t) for t in defs)
    out += b"".join(b"Y" + enc_thm(t) for t in typedefs)
    for n, t in named:
        out += b"T%d:%s" % (len(n), n.encode()) + enc_thm(t)
    return out + b"S"


def read(path):
    with open(path) as f:
        return f.read()


def render(tm, defs=()):
    theory = c.Theory([((), d) for d in defs], [])
    return c.Renderer(theory).theorem(((), tm))


BYTE = (
    "t",
    "word",
    (("t", "tybit0", (("t", "tybit0", (("t", "tybit0", (("t", "1", ()),)),)),)),),
)


def byte_list_term(bs):
    word = const("word", fun(NUM, BYTE))
    tm = const("NIL", list_of(BYTE))
    cons = const("CONS", fun(BYTE, fun(list_of(BYTE), list_of(BYTE))))
    for b in reversed(bs):
        tm = app(cons, app(word, num(b)), tm)
    return tm


def list_term(xs):
    ty = c.TypeOf()(xs[0])
    tm = const("NIL", list_of(ty))
    cons = const("CONS", fun(ty, fun(list_of(ty), list_of(ty))))
    for x in reversed(xs):
        tm = app(cons, x, tm)
    return tm


IND = ("t", "ind", ())


def background():
    """Definitions and type definitions for the constants and types that
    the tests use, with bodies built from `=` alone."""
    defs, typedefs = [], []

    def define(name, ty):
        # c = @y. y = y, using only primitive constants.
        at = fun(fun(ty, BOOL), ty)
        y = var("y", ty)
        body = app(const("@", at), lam(y, eq(y, y, ty)))
        defs.append(eq(const(name, ty), body, ty))

    def typedef(name, args):
        aty = ("t", name, tuple(args))
        r = var("r", IND)
        pred = const("P_" + name, fun(IND, BOOL))
        define("P_" + name, fun(IND, BOOL))
        rep = const("dest_" + name, fun(aty, IND))
        abs_ = const("mk_" + name, fun(IND, aty))
        typedefs.append(eq(app(pred, r), eq(app(rep, app(abs_, r)), r, IND), BOOL))

    for n in ["_0"]:
        define(n, NUM)
    for n in ["NUMERAL", "BIT0", "BIT1"]:
        define(n, fun(NUM, NUM))
    N = ("v", "N")
    define("word", fun(NUM, ("t", "word", (N,))))
    define("CONS", fun(A, fun(list_of(A), list_of(A))))
    define("NIL", list_of(A))
    typedef("num", [])
    typedef("list", [A])
    typedef("word", [N])
    typedef("tybit0", [A])
    typedef("1", [])
    return defs, typedefs


class Render(unittest.TestCase):
    def test_distinct_objects_render_differently(self):
        x_num, x_bool = var("x", NUM), var("x", BOOL)
        terms = [
            lam(x_num, x_num),
            lam(x_num, const("x", NUM)),
            lam(x_num, lam(x_bool, x_num)),
            lam(x_num, lam(x_bool, x_bool)),
            lam(x_num, var("x", A)),
            var("x", NUM),
            const("x", NUM),
            const("x y", NUM),
            const("x", A),
            app(const("f", fun(NUM, NUM)), num(0)),
            app(const("f", fun(NUM, NUM)), num(1)),
            app(
                const("NUMERAL", fun(NUM, NUM)),
                app(const("BIT0", fun(NUM, NUM)), const("_0", NUM)),
            ),
            const("NIL", list_of(NUM)),
            const("NIL", list_of(BOOL)),
            app(const("int_of_num", fun(NUM, INT)), num(3)),
            app(const("int_of_num", fun(NUM, NUM)), num(3)),
            const("int_of_num", fun(NUM, INT)),
            const("p", prod(prod(NUM, NUM), NUM)),
            const("p", prod(NUM, prod(NUM, NUM))),
            const("p", ("t", "#", (NUM, NUM))),
            byte_list_term([1, 2]),
            byte_list_term([1, 258]),
            list_term([app(const("word", fun(NUM, BYTE)), num(1))]),
            list_term([num(1), num(2)]),
        ]
        rendered = [render(eq(t, t, c.TypeOf()(t))) for t in terms]
        self.assertEqual(len(set(rendered)), len(rendered), rendered)

    def test_binders_and_chains(self):
        AND = const("/\\", fun(BOOL, fun(BOOL, BOOL)))
        ALL = const("!", fun(fun(NUM, BOOL), BOOL))
        a, b, d = (var(n, BOOL) for n in "abd")
        x, y = var("x", NUM), var("y", NUM)
        # Generic types, so that neither constant needs a type annotation.
        P = var("P", fun(A, BOOL))
        defs = [
            eq(AND, lam(a, lam(b, a)), fun(BOOL, fun(BOOL, BOOL))),
            eq(
                const("!", fun(fun(A, BOOL), BOOL)),
                lam(P, app(P, var("z", A))),
                fun(fun(A, BOOL), BOOL),
            ),
        ]
        right = app(AND, a, app(AND, b, d))
        left = app(AND, app(AND, a, b), d)
        self.assertEqual(render(right, defs), "|- (/\\ {a:bool} {b:bool} {d:bool})")
        self.assertNotEqual(render(right, defs), render(left, defs))
        nested = app(ALL, lam(x, app(ALL, lam(y, eq(x, y)))))
        self.assertEqual(render(nested, defs), "|- (!x:num y:num. (= x y))")
        # The binder must be applied to an abstraction to be printed as one.
        p = var("p", fun(NUM, BOOL))
        self.assertEqual(render(app(ALL, p), defs), "|- (! {p:(num -> bool)})")
        shadowed = app(ALL, lam(x, app(ALL, lam(x, eq(x, x)))))
        self.assertNotEqual(render(nested, defs), render(shadowed, defs))

    def test_variable_names_print_alike(self):
        # A variable named + is quoted in its binder and in the body;
        # inside that binder, the constant + is marked with $.
        plus = var("+", NUM)
        add = const("+", fun(NUM, NUM))
        tm = lam(plus, app(add, plus))
        body = '(\\"+":num. ($+:(num -> num) "+"))'
        self.assertEqual(render(eq(tm, tm, fun(NUM, NUM))), f"|- (= {body} {body})")
        self.assertEqual(render(eq(plus, plus)), '|- (= {"+":num} {"+":num})')

    def test_notation(self):
        f = const("f", fun(NUM, NUM))
        self.assertEqual(
            render(eq(app(f, num(12)), num(0))), "|- (= (f:(num -> num) #12) #0)"
        )
        x = var("x", NUM)
        self.assertEqual(
            render(app(const("!", fun(fun(NUM, BOOL), BOOL)), lam(x, eq(x, x)))),
            "|- (!:((num -> bool) -> bool) (\\x:num. (= x x)))",
        )
        # A non-canonical numeral is printed as written.
        odd = app(
            const("NUMERAL", fun(NUM, NUM)),
            app(const("BIT0", fun(NUM, NUM)), const("_0", NUM)),
        )
        self.assertIn("BIT0", render(eq(odd, odd)))
        # Integer literals and product types.
        i = app(const("int_of_num", fun(NUM, INT)), num(3))
        self.assertEqual(render(eq(i, i, INT)), "|- (= &3 &3)")
        p = const("p", prod(NUM, prod(BOOL, NUM)))
        self.assertEqual(
            render(eq(p, p, p[2])), "|- (= p:(num # bool # num) p:(num # bool # num))"
        )
        # Byte lists in hex, unless an element is not a canonical byte.
        bl = byte_list_term([1, 255])
        self.assertEqual(
            render(eq(bl, bl, list_of(BYTE))), "|- (= #x[01 ff] #x[01 ff])"
        )
        odd = byte_list_term([1, 256])
        self.assertIn(
            "[(word:(num -> (word #8)) #1);", render(eq(odd, odd, list_of(BYTE)))
        )
        # Long lists fill their lines.
        nums = app(
            const("f", fun(list_of(NUM), BOOL)), list_term([num(n) for n in range(40)])
        )
        self.assertIn("#3; #4;", render(nums))

    def test_genvars_are_renumbered(self):
        def tm(a, b):
            va, vb = var(a, NUM), var(b, NUM)
            return lam(va, lam(vb, eq(va, vb)))

        self.assertEqual(
            render(eq(tm("_17", "_9"), tm("_17", "_9"), fun(NUM, fun(NUM, BOOL)))),
            render(eq(tm("_3", "_2"), tm("_3", "_2"), fun(NUM, fun(NUM, BOOL)))),
        )
        # Still a bijection: swapping roles changes the text.
        self.assertNotEqual(
            render(tm("_1", "_2")),
            render(
                lam(
                    var("_1", NUM),
                    lam(var("_2", NUM), eq(var("_2", NUM), var("_1", NUM))),
                )
            ),
        )
        # A constant whose name matches a renumbered variable is marked.
        self.assertIn(
            "$_1", render(lam(var("_9", NUM), eq(var("_9", NUM), const("_1", NUM))))
        )

    def test_typedef_shows_argument_order(self):
        # Two type definitions that differ only in the order of the new
        # type's arguments.
        def rth(args):
            aty = ("t", "pair", args)
            rty = fun(A, B)
            r = var("r", rty)
            pred = lam(var("f", rty), const("T", BOOL))
            rep = const("dest_pair", fun(aty, rty))
            abs_ = const("mk_pair", fun(rty, aty))
            return ((), eq(app(pred, r), eq(app(rep, app(abs_, r)), r, rty), BOOL))

        def text(args):
            th = rth(args)
            theory = c.Theory([], [th])
            return c.Renderer(theory).theorem(th, theory.typedef_consts["pair"])

        self.assertNotEqual(text((A, B)), text((B, A)))

    def test_invented_type_variables_are_renumbered(self):
        def tm(a, b):
            f = var("f", fun(("v", a), ("v", b)))
            return lam(f, eq(f, f, fun(("v", a), ("v", b))))

        self.assertEqual(render(tm("?17", "?3")), render(tm("?4", "?9")))
        self.assertNotEqual(render(tm("?17", "?3")), render(tm("?17", "?17")))
        self.assertNotEqual(render(tm("?17", "?3")), render(tm("A", "?3")))
        self.assertIn("(\\f:('?1 -> '?2).", render(tm("?17", "?3")))
        # Other names that are not alphanumeric stay quoted.
        self.assertIn('\'"?x"', render(tm("?x", "?3")))

    def test_polymorphic_constants(self):
        # Without a known generic type a constant is annotated; with one,
        # only when its arguments do not determine the instance.
        f = const("f", fun(NUM, NUM))
        defs = [eq(const("f", fun(A, A)), lam(var("x", A), var("x", A)), fun(A, A))]
        self.assertEqual(
            render(eq(app(f, num(1)), num(1))), "|- (= (f:(num -> num) #1) #1)"
        )
        self.assertEqual(render(eq(app(f, num(1)), num(1)), defs), "|- (= (f #1) #1)")
        self.assertIn("f:(num -> num)", render(eq(f, f, fun(NUM, NUM)), defs))

    def test_long_terms_break(self):
        f = const("f", fun(NUM, fun(NUM, NUM)))
        tm = num(1)
        for k in range(30):
            tm = app(f, tm, num(k))
        text = render(eq(tm, tm))
        self.assertTrue(all(len(line) <= 120 for line in text.split("\n")))
        self.assertGreater(len(text.split("\n")), 1)


class Conform(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.defs = os.path.join(self.dir, "accepted.defs")
        self.thms = os.path.join(self.dir, "accepted.thms")
        self.code = bytes([1, 2, 3])
        self.mc = const("mc", list_of(BYTE))
        self.mc_def = eq(self.mc, byte_list_term(list(self.code)), list_of(BYTE))
        self.k = const("K", NUM)
        self.k_def = eq(self.k, num(7))
        self.ax = eq(num(0), num(0))
        stmt = eq(app(const("LENGTH", fun(list_of(BYTE), NUM)), self.mc), self.k)
        self.length_def = eq(
            const("LENGTH", fun(list_of(A), NUM)),
            lam(var("l", list_of(A)), num(3)),
            fun(list_of(A), NUM),
        )
        self.named = [("THM", stmt)]
        # The generated layer: the axiom and the background theory.
        self.layer = os.path.join(self.dir, "layer.defs")
        defs, typedefs = background()
        theory = c.Theory([((), d) for d in defs], [((), t) for t in typedefs])
        render = c.Renderer(theory)
        entries = {
            c.axiom_header(render.theorem(((), self.ax))): render.theorem(((), self.ax))
        }
        for d in defs:
            entries[f"definition {c.qname(c.dest_eq(d)[0][1])}"] = render.theorem(
                ((), d)
            )
        for name, th in theory.type_def.items():
            entries[f"typedef {name}"] = render.theorem(th, theory.typedef_consts[name])
        c.write_entries(self.layer, "", entries)

    def check(
        self,
        accept=False,
        accept_hashed=False,
        names=("THM",),
        raw=None,
        **kw,
    ):
        defs, typedefs = background()
        data = dict(
            axioms=[self.ax],
            defs=[self.mc_def, self.k_def, self.length_def],
            named=self.named,
        )
        data.update(kw)
        data["defs"] = list(data["defs"]) + data.pop("background", defs)
        data["typedefs"] = typedefs + list(data.pop("extra_typedefs", []))
        path = os.path.join(self.dir, "r.result")
        with open(path, "wb") as f:
            f.write(result(**data) if raw is None else raw)
        return c.conform(
            path,
            "a/f",
            list(names),
            [self.layer],
            self.defs,
            self.thms,
            accept,
            accept_hashed,
        )

    def test_accept_then_check(self):
        with self.assertRaisesRegex(c.Failed, "not accepted"):
            self.check()
        self.check(accept=True)
        self.check()
        text = read(self.defs)
        self.assertIn("definition K", text)
        # A byte list is shown in hex, after a note on its bytes.
        note = c.byte_note("mc", self.code)
        self.assertIn(f"{note}\ndefinition mc\n  |- (= mc #x[01 02 03])", text)
        self.assertEqual(
            c.rendered_bytes(c.read_entries(self.defs)["definition mc"]),
            ("mc", self.code),
        )

    def test_changed_byte_list_fails(self):
        self.check(accept=True)
        mc_def = eq(self.mc, byte_list_term([1, 2, 4]), list_of(BYTE))
        with self.assertRaisesRegex(c.Failed, "definition mc differs"):
            self.check(defs=[mc_def, self.k_def, self.length_def])

    def test_changed_definition_fails(self):
        self.check(accept=True)
        with self.assertRaisesRegex(c.Failed, "definition K differs"):
            self.check(defs=[self.mc_def, eq(self.k, num(8)), self.length_def])

    def test_undefined_constant_fails(self):
        with self.assertRaisesRegex(c.Failed, "constant K has no definition"):
            self.check(accept=True, defs=[self.mc_def, self.length_def])

    def test_unreached_definitions_are_ignored(self):
        self.check(accept=True)
        extra = eq(const("UNUSED", NUM), num(1))
        self.check(defs=[self.mc_def, self.k_def, self.length_def, extra])

    def test_large_definitions_are_hashed(self):
        def big(name):
            v = var(name * 40000, NUM)
            return eq(const("K", NUM), app(lam(v, v), num(7)))

        defs = [self.mc_def, big("v"), self.length_def]
        with self.assertRaisesRegex(c.Failed, "accepted as hashes.*definition K"):
            self.check(accept=True, defs=defs)
        self.check(accept=True, accept_hashed=True, defs=defs)
        self.assertIn("definition K\n  sha256 ", read(self.defs))
        self.check(defs=defs)
        with self.assertRaisesRegex(c.Failed, "definition K differs"):
            self.check(defs=[self.mc_def, big("w"), self.length_def])

    def test_large_theorem_is_never_accepted(self):
        v = var("v" * 70000, NUM)
        stmt = eq(app(lam(v, v), self.k), self.k)
        with self.assertRaisesRegex(c.Failed, "THM is too large"):
            self.check(accept=True, accept_hashed=True, named=[("THM", stmt)])

    def test_wrong_theorem_list_fails(self):
        with self.assertRaisesRegex(c.Failed, "wrong theorem list"):
            self.check(accept=True, names=("THM", "OTHER"))

    def test_constant_defined_twice_fails(self):
        with self.assertRaisesRegex(c.Failed, "constant K is defined twice"):
            self.check(accept=True, defs=[self.mc_def, self.k_def, self.k_def])
        with self.assertRaisesRegex(c.Failed, "constant @ is defined twice"):
            self.check(accept=True, defs=[eq(const("@", NUM), num(0))])

    def test_undefined_type_fails(self):
        k = const("K", ("t", "opaque", ()))
        stmt = eq(k, k, k[2])
        with self.assertRaisesRegex(c.Failed, "type opaque has no definition"):
            self.check(accept=True, named=[("THM", stmt)])

    def test_changed_type_definition_fails(self):
        # A proof's own type, reached through the statement.
        aty = ("t", "own", ())
        r = var("r", IND)

        def typedef(pred):
            rep = const("dest_own", fun(aty, IND))
            abs_ = const("mk_own", fun(IND, aty))
            return eq(app(pred, r), eq(app(rep, app(abs_, r)), r, IND), BOOL)

        k = const("K", aty)
        stmt = eq(k, k, aty)
        k_def = eq(k, app(const("mk_own", fun(IND, aty)), var("i", IND)), aty)
        p, q = const("P", fun(IND, BOOL)), const("Q", fun(IND, BOOL))
        pq_defs = [
            eq(p, lam(r, eq(r, r, IND)), fun(IND, BOOL)),
            eq(q, lam(r, eq(r, r, IND)), fun(IND, BOOL)),
        ]
        kw = dict(defs=[self.mc_def, k_def, self.length_def] + pq_defs)
        named = [("THM", stmt), ("CODE", self.named[0][1])]
        names = ("THM", "CODE")
        self.check(True, names=names, named=named, extra_typedefs=[typedef(p)], **kw)
        self.assertIn("typedef own", read(self.defs))
        with self.assertRaisesRegex(c.Failed, "typedef own differs"):
            self.check(names=names, named=named, extra_typedefs=[typedef(q)], **kw)

    def test_malformed_results_fail(self):
        good = result(axioms=[self.ax])
        for raw, msg in [
            (b"HOLTRACE-RESULT-4\nS", "no valid header"),
            (c.RESULT_MAGIC + b"F4:oops", "oops"),
            (good[:-1], "truncated"),
            (good + b"S", "continues after its end"),
            (c.RESULT_MAGIC + b"Q", "bad record"),
        ]:
            with self.assertRaisesRegex(c.Failed, msg):
                self.check(accept=True, raw=raw)

    def test_new_axiom_is_never_accepted(self):
        with self.assertRaisesRegex(c.Failed, "not an accepted axiom"):
            self.check(accept=True, axioms=[self.ax, eq(num(1), num(2))])

    def test_only_the_first_layer_lists_axioms(self):
        later = os.path.join(self.dir, "later.defs")
        text = c.Renderer(c.Theory([], [])).theorem(((), eq(num(1), num(2))))
        c.write_entries(later, "", {c.axiom_header(text): text})
        with self.assertRaisesRegex(c.Failed, "later.defs lists axiom .*only HOL"):
            c.read_layers([self.layer, later])

    def test_changed_layer_definition_is_never_accepted(self):
        defs, _ = background()
        changed = [
            eq(const("_0", NUM), app(const("NUMERAL", fun(NUM, NUM)), const("_0", NUM)))
            if c.dest_eq(d)[0][1] == "_0"
            else d
            for d in defs
        ]
        with self.assertRaisesRegex(c.Failed, "definition _0 differs from"):
            self.check(accept=True, background=changed)

    def test_unused_entries_are_removed(self):
        self.check(accept=True)
        stmt = eq(app(const("LENGTH", fun(list_of(BYTE), NUM)), self.mc), num(3))
        with self.assertRaisesRegex(c.Failed, "definition K is no longer used"):
            self.check(named=[("THM", stmt)])
        self.check(accept=True, named=[("THM", stmt)])
        self.assertNotIn("definition K", read(self.defs))

    def test_changed_statement_fails(self):
        self.check(accept=True)
        stmt = eq(app(const("LENGTH", fun(list_of(BYTE), NUM)), self.mc), num(3))
        with self.assertRaisesRegex(c.Failed, "theorem a/f THM differs"):
            self.check(named=[("THM", stmt)])


if __name__ == "__main__":
    unittest.main()
