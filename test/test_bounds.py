# Copyright (c) 2024-2025 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

#
# The purpose of this script is to provide either brute-force proof
# or empirical evidence to arithmetic bounds for the modular
# arithmetic primitives used in this repository.
#

import random
from functools import lru_cache

# Global constants
R = 2**16
Q = 3329
Qinv = pow(-Q, -1, R)

#
# Barrett multiplication via doubling
#


def round_even(x):
    return 2 * round(x / 2)


@lru_cache(maxsize=None)
def barrett_twiddle(b):
    """Compute twiddle required for Barrett multiplications
    via doubling-high-multiply."""
    return round_even(b * R / Q) // 2


def sqrdmulh_i16(a, b):
    """Doubling multiply high with rounding"""
    # We cannot use round() here because of its behaviour
    # on multiples of 0.5: round(-.5) = round(0.5) = 0
    return (2 * a * b + 2**15) // 2**16


def barmul(a, b):
    """Compute doubling Barrett multiplication of a and b"""
    b_twiddle = barrett_twiddle(b)
    return a * b - Q * sqrdmulh_i16(a, b_twiddle)


#
# Montgomery multiplication
#


def lift_signed_i16(x):
    """Returns signed canonical representative modulo R=2^16."""
    x = x % R
    if x >= R // 2:
        x -= R
    return x


@lru_cache(maxsize=None)
def montmul_neg_twiddle(b):
    return (b * Qinv) % R


def montmul_neg(a, b):
    b_twiddle = montmul_neg_twiddle(b)
    return (a * b + Q * lift_signed_i16(a * b_twiddle)) // R


#
# Generic test functions
#


def test_all_i16(f):
    for a in range(-R // 2, R // 2):
        if a % 1000 == 0:
            print(f"{a} ...")
        for b in range(-Q // 2, Q // 2):
            f(a, b)
            f(-a, b)


def test_random(f, num_tests=10000000, bound=2 * R):
    print(f"Randomly checking Barrett<->Montgomery relation ({num_tests} tests)...")
    for i in range(num_tests):
        if i % 100000 == 0:
            print(f"... run {i} tests ({((i * 1000) // num_tests)/10}%)")
        a = random.randrange(-bound, bound)
        b = random.randrange(-bound, bound)
        f(a, b)


#
# Test relation between Barrett and Montgomery multiplication
# (Proposition 1 in https://eprint.iacr.org/2021/986.pdf)
#


@lru_cache(maxsize=None)
def modq_even(a):
    return a - Q * round_even(a / Q)


def barmul_test(a, b):
    bp = modq_even(b * R)
    r0 = barmul(a, b)
    r1 = montmul_neg(a, bp)
    if r0 != r1:
        print(f"barmul test failure for {a,b}!")
        print(f"Barrett multiplication: {r0}")
        print(f"Montgomery multiplication: {r1} (factor {bp})")
        assert False


def bar_mont_test_all_i16():
    test_all_i16(barmul_test)


def bar_test_random():
    test_random(barmul_test)


#
# Test bound on Barrett multiplication
#
# |barmul(a,b)| < Q*(0.0508*C + 1/2) if |a| < C*q
#
# where 0.0508 appears as a close upper bound for Q/2**16.
#


def bar_bound_test(a, b, max_scale=[]):
    if a == 0:
        return
    C = abs(a) / Q
    ab = barmul(a, b)
    Cp = abs(ab) / Q
    scale_bound = 0.0508  # Upper bound to Q/2**16
    scale = (Cp - 1 / 2) / C
    if len(max_scale) == 0 or scale > max_scale[-1]:
        max_scale.append(scale)
        print(f"New scale bound for {(a,b)}: {scale}")
    if Cp >= scale_bound * C + 1 / 2:
        print(f"bar bound test failure for (a,b)={(a,b)}")
        print(f"barmul(a,b): {ab}")
        print(f"C  (=a/q): {C}")
        print(f"Cp (=barmul(a,b)/q): {Cp}")
        assert False


def bar_bound_test_all_i16():
    test_all_i16(bar_bound_test)


#
# NTT bounds progression
#


def funciter(f, n, x):
    """Compute f^n(x)"""
    if n == 0:
        return x
    return funciter(f, n - 1, f(x))


def ntt_layer_bound_growth(factor):
    """If the inputs to a CT-based layer of the NTT are bound by C*Q,
    the outputs are bound by C'*Q, where C' is the return value of this
    function."""

    # Each coefficient is replaced by a +- t*b where a,b are input coefficients,
    # t is a suitable twiddle, and * is Barrett multiplication. a is thus bound
    # by C*q, while t*b is bound by 0.0508*C + 1/2 (see above).
    return lambda C: C + factor * C + 1 / 2


def ntt_layer_bound(factor, layers=7, initial=Q):
    """Returns a bound on the absolute value of coefficients after a fixed number
    of layers, assuming an initial absolute bound `initial`."""
    return funciter(ntt_layer_bound_growth(factor), layers, initial / Q)


barmul_ntt_layer_bound = ntt_layer_bound(0.0508)
montmul_ntt_layer_bound = ntt_layer_bound(0.0204)
