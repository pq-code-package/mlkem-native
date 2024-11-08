[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# CBMC Proof Guide and Cookbook for mlkem-native

This doc acts as a guide to developing proofs of C code using [CBMC](https://model-checking.github.io/cbmc-training/). It concentrates
on the use of _contracts_ to achieve _unbounded_ and _modular_ proofs of type-safety
and correctness properties.

This document uses the abbreviated forms of the [CBMC contracts](https://diffblue.github.io/cbmc/contracts-user.html) defined by macros in the
[cbmc.h](../../mlkem/cbmc.h) header file in the mlkem-native sources.

## Common Proof Patterns

### Loops (general advice)

1. A function should contain at most one outermost loop statement. If the function you're trying to prove has more than one outermost loop, then re-factor it into two or more functions.

2. The one outermost loop statement should be the _final_ statement before the function returns. Don't have complicated code _after_ the loop body.

### `for` loops

The most common, and easiest, patten is a "for" loop that has a counter starting at 0, and counting up to some upper bound, like this:

```
for (int i = 0; i < C; i++) {
    S;
}
```
Notes:
1. It is good practice to declare the counter variable locally, within the scope of the loop.
2. The counter variable should be a constant within the loop body. In the example above, do _not_ modify (or take the address of) `i` in the body of the loop.
3. `int` is the best type for the counter variable. `unsigned` integer types complicate matters with their modulo N semantics. Avoid `size_t` since its large range (possibly unsigned 64 bit) can slow proofs down.

CBMC requires basic assigns, loop-invariant, and decreases contracts _in exactly that order_. Note that the contracts appear _before_ the opening `{` of the loop body, so we also need to tell `clang-format` not to reformat these lines. The basic pattern is thus:

```
for (int i = 0; i < C; i++)
    // clang-format off
ASSIGNS(i) // plus whatever else S does
INVARIANT(i >= 0)
INVARIANT(i <= C)
DECREASES(C - i)
// clang-format on
{
    S;
}
```

The `i <= C` in the invariant is _not_ a typo. CBMC places the invariant just _after_ the loop counter has been incremented, but just _before_ the loop exit test, so it is possible for `i == C` at the invariant on the final iteration of the loop.

### Iterating over an array for a `for` loop

A common pattern - doing something to every element of an array. An example would be setting every element of a byte-array to 0x00 given a pointer to the first element and a length. Initially, we want to prove type safety of this function, so we won't even bother with a post-condition. The function specification might look like this:

```
void zero_array_ts (uint8_t *dst, int len)
    // clang-format off
REQUIRES(IS_FRESH(dst, len))
ASSIGNS(OBJECT_WHOLE(dst));
// clang-format on
```

The `IS_FRESH(dst,len)` in the precondition means that the pointer value `dst` is not `NULL` and is pointing to at least `len` bytes of data. The `ASSIGNS` contract (in this case) means that when the function returns, it promises to have updated the whole object pointed to by dst - in this case `len` bytes of data.

The body:

```
void zero_array_ts (uint8_t *dst, int len)
{
    for (int i = 0; i < len; i++)
        // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(dst))
    INVARIANT(i >= 0 && i <= len)
    DECREASES(len - i)
    // clang-format on
    {
        dst[i] = 0;
    }
}
```
The only real "type safety proofs" here are that
1. dst is pointing at exactly "len" bytes - this is given by the IS_FRESH() part of the precondition.
2. The assignment to `dst[i]` does not have a buffer overflow. This requires a proof that `i >= 0 && i < len` which is trivially discharged given the loop invariant AND the fact that the loop _hasn't_ terminated (so we know `i < len` too).

### Correctness proof of zero_array

We can go further, and prove the correctness of that function by adding a post-condition, and extending the loop invariant. This introduces more important patterns.

The function specification is extended:

```
void zero_array_correct (uint8_t *dst, int len)
    // clang-format off
REQUIRES(IS_FRESH(dst, len))
ASSIGNS(OBJECT_WHOLE(dst))
ENSURES(FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 });
// clang-format on
```

Note the required order of the contracts is always REQUIRES, ASSIGNS, ENSURES.

The body is the same, but with a stronger loop invariant. The invariant says that "after j loop iterations, we've zeroed the first j elements of the array", so:

```
void zero_array_correct (uint8_t *dst, int len)
{
    for (int i = 0; i < len; i++)
        // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(dst))
    INVARIANT(i >= 0 && i <= len)
    INVARIANT(FORALL { int j; (0 <= j && j <= i - 1) ==> dst[j] == 0 } )
    DECREASES(len - i)
    // clang-format on
    {
        dst[i] = 0;
    }
}
```

Rules of thumb:
1. Don't overload your program variables with quantified variables inside your FORALL contracts. It get confusing if you do.
2. The type of the quanitified variable is _signed_ "int". This is important.
3. The path in the program from the loop-invariant, through the final loop exit test, to the implicit `return` statement is "nothing" or a "null statement". The proof needs to establish that (on the final iteration), the loop invariant _and_ the loop exit condidtion imply the post-condition. Imagine having to do that if there's some really complex code _after_ the loop body.

This pattern also brings up another important trick - the use of "null ranges" in FORALL expressions. Consider the loop invariant above. We need to prove that it's true on the first entry to the loop (i.e. when i == 0).

Substituting i == 0 into there, we need to prove

```
FORALL { int j; (0 <= j && j <= -1) ==> dst[j] == 0 }
```

but how can j be both larger-than-or-equal-to 0 AND less-than-or-equal-to -1 at the same time? Answer: it can't! So.. the left hand side of the quantified predicate is False, so it reduces to:

```
FORALL { int j; false ==> dst[j] == 0 }
```

The `==>` is a logical implication, and we know that `False ==> ANYTHING` is True, so all is well.

This comes up a lot. You often end up reasoning about such "slices" of arrays, where one or more of the slices has "null range" at either the loop entry, or at the loop exit point, and therefore that particular quantifier "disappears". Several examples of this trick can be found on the MLKEM codebase.

This also explains why we prefer to use _signed_ integers for loop counters and quantified variables - to allow "0 - 1" to evaluate to -1.  If you use an unsigned type, then "0 - 1" evaluated to something like UINT_MAX, and all hell breaks loose.

## Invariant && loop-exit ==> post-condition

Another important sanity check. If there are no statements following the loop body, then the loop invariant AND the loop exit condition should imply the post-condition. For the example above, we need to prove:

```
// Loop invariant
(i >= 0 &&
 i <= len &&
 (FORALL { int j; (0 <= j && j <= i - 1) ==> dst[j] == 0 } )
&&
// Loop exit condition must be TRUE, so
i == len)

  ==>

// Post-condition
FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 }
```

The loop exit condition means that we can just replace `i` with `len` in the hypotheses, to get:

```
len >= 0 &&
len <= len &&
(FORALL { int j; (0 <= j && j <= len - 1) ==> dst[j] == 0 } )
  ==>
FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 }
```

`j <= len - 1` can be simplified to `j < len` so that simplifies to:

```
FORALL { int j; (0 <= j && j < len) ==> dst[j] == 0 }
  ==>
FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 }
```

which is True.

## Recipe to prove a new function

Let's say we want to develop a proof of a function. Here are the basic steps.
1. Populate a proof directory
2. Update Makefile
3. Update harness function
4. Supply top-level contracts for the function
5. Supply loop-invariants (if required) and other interior contracts
6. Prove it!

These steps are expanded on in the following sub-sections

### Populate a proof directory

For mlkem-native, proof directories lie below `cbmc/proofs`

Create a new sub-directory in there, where the name of the directory is the name of the function _without_ the `$(MLKEM_NAMESPACE)` prefix.

That directory needs to contain 3 files.

* cbmc-proof.txt
* Makefile
* XXX_harness.c

where "XXX" is the name of the function being proved - same as the directory name.

We suggest that you copy these files from an existing proof directory and modify the latter two. The `cbmc-proof.txt` file is just a marker that says "this directory contains a CBMC proof" to the tools, so no modification is required.

### Update Makefile

The `Makefile` sets options and targets for this proof. Let's imagine that the function we want to prove is called `XXX` (without the `$(MLKEM_NAMESPACE)` prefix).

Edit the Makefile and update the definition of the following variables:

* HARNESS_FILE - should be `XXX_harness`
* PROOF_UID - should be `XXX`
* PROJECT_SOURCES - should the files containing the source code of XXX
* CHECK_FUNCTION_CONTRACTS - set to the `XXX`, but _with_ the `$(MLKEM_NAMESPACE)` prefix if required
* USE_FUNCTION_CONTRACTS - a list of functions that `XXX` calls where you want CBMC to use the contracts of the called function for proof, rather than 'inlining' the called function for proof. Include the `$(MLKEM_NAMESPACE)` prefix if required
* EXTERNAL_SAT_SOLVER - should _always_ be "nothing" to prevent CBMC selecting a SAT backend over the selected SMT backend.
* CBMCFLAGS - additional flags to pass to the final run of CBMC. This is normally set to `--smt2` which tells cbmc to run Z3 as its underlying solver. Can also be set to `--bitwuzla` which is sometimes better at generaing counter-examples when Z3 fails.
* FUNCTION_NAME - set to `XXX` with the `$(MLKEM_NAMESPACE)` prefix if required
* CBMC_OBJECT_BITS. Normally set to 8, but might need to be increased if CBMC runs out of memory for this proof.

For documentation of these (and the other) options, see the `cbmc/proofs/Makefile.common` file.

The `USE_FUNCTION_CONTRACTS` option should be used where possible, since contracts enable modular proof, which is far more efficient
 than inlining, which tends to explode in complexity for higher-level functions.

#### Z3 or Bitwuzla?

We have found that it's better to use Bitwuzla in the initial stages of developing and debugging a new proof.

When Z3 finds that a proof is "sat" (i.e. not true), it tries to produce a counter-example to show you what's wrong. Unfortunately, recent versions of Z3 can produce quantified expressions as output that cannot be currently understood by CBMC. This leads CBMC to fail with an error such as

```
SMT2 solver returned non-constant value for variable Bxxx
```

This is not helpful when trying to understand a failed proof. Bitwuzla works better and produces reliable counter-examples.

Once a proof is working OK, we revert to Z3 to check it _also_ works with Z3. If it does, then keep Z3 as the selected prover. If not, then stick with Bitwuzla.


### Update harness function

The file `XXX_harness.c` should declare a single function called `XXX_harness()` that calls `XXX` exactly once, with appropriately typed actual parameters. The actual parameters should be variables of the simplest type possible, and should be _uninitialized_. Where a pointer value is required, create an uninitialized variable of that pointer type. Do _not_ pass the address of a stack-allocated object.

For example, if a function f() expects a single parameter which is a pointer to some struct s:
```
void f(s *x)
REQUIRES(IS_FRESH(x, sizeof(s));
```
then the harness should contain
```
  s *a; // uninitialized raw pointer
  f(a);
```
The harness should _not_ contain
```
  s a;
  f(&a);
```

Using contracts, this harness function should not need to contain any CBMC `ASSUME` or `ASSERT` statements at all.

### Supply top-level contracts

Now for the tricky bit. Does `XXX` need any top-level pre- and post-condition contracts, other than those inferred from its type-signature?

A common case is where a function has an array parameter, where the numeric range of the array's elements are not just the range of the underlying predefined type.

Similarly, a parameter of a predefined integer type might have to be constrained to a small range.

Check for any BOUND macros in the body that give range constraints on the parameters, and make sure that your contracts are identical or consistent with those. Also read the comments for XXX to make sure they agree with your contracts.

The order of the top-level contracts for a function is _always_:
```
t1 XXX(params...)
    // clang-format off
REQUIRES()
ASSIGNS()
ENSURES();
// clang-format on
```
with a final semi-colon on the end of the last one. That final semi-colon is needed to terminate the function declaration as per normal C syntax.

### Interior contracts and loop invariants

If XXX contains no loop statements, then you might be able to just skip this step.

As above, it's best if a function contains at most ONE top-level loop statement. Refer to the patterns above for common invariants. Don't be afraid to ask for help.

### Prove it!

Proof of a single function can be run from the proof directory for that function with `make result`.

This produces `logs/result.txt` in plaintext format.

Before pushing a new proof for a new function, make sure that _all_ proofs run OK from the `cbmc/proofs` directory with

```
export MLKEM_K=3 # or 2 or 4...
./run-cbmc-proofs.py --summarize -j$(nproc)
```

That will use `$(nproc)` processor cores to run the proofs.

### Debugging a proof

If a proof fails, you can run

```
make result VERBOSE=1 >log.txt
```

and then inspect `log.txt` to see the exact sequence of commands that has been run. With that, you should be able to reproduce a failure on the command-line directly.

## Worked Example - proving poly_tobytes()

This section follows the recipe above, and adds actual settings, contracts and command to prove the `poly_tobytes()` function.

### Populate a proof directory

The proof directory is `cbmc/proofs/poly_tobytes`

### Update Makefile

The significant changes are:
```
HARNESS_FILE = poly_tobytes_harness
PROOF_UID = poly_tobytes
PROJECT_SOURCES += $(SRCDIR)/mlkem/poly.c
CHECK_FUNCTION_CONTRACTS=$(MLKEM_NAMESPACE)poly_tobytes
USE_FUNCTION_CONTRACTS=
FUNCTION_NAME = $(MLKEM_NAMESPACE)poly_tobytes
```
Note that `USE_FUNCTION_CONTRACTS` is left empty since `poly_tobytes()` is a leaf function that does not call any other functions at all.

### Update harness function

`poly_tobytes()` has a simple API, requiring two parameters, so the harness function is:

```
void harness(void) {
  poly *a;
  uint8_t *r;

  /* Contracts for this function are in poly.h */
  poly_tobytes(r, a);
}
```

### Top-level contracts

The comments on `poly_tobytes()` give us a clear hint:

```
 * Arguments:   INPUT:
 *              - a: const pointer to input polynomial,
 *                with each coefficient in the range [0,1,..,Q-1]
 *              OUTPUT
 *              - r: pointer to output byte array
 *                   (of MLKEM_POLYBYTES bytes)
```
So we need to write a REQUIRES contract to constrain the ranges of the coefficients denoted by the parameter `a`. There is no constraint on the output byte array, other than it must be the right length, which is given by the function prototype.

We can use the macros in `cbmc.h` to help, thus:

```
void poly_tobytes(uint8_t r[MLKEM_POLYBYTES], const poly *a)
     // clang-format off
REQUIRES(IS_FRESH(a, sizeof(poly)))
REQUIRES(ARRAY_IN_BOUNDS(int, k, 0, (MLKEM_N - 1), a->coeffs, 0, (MLKEM_Q - 1)))
ASSIGNS(OBJECT_WHOLE(r));
// clang-format on
```

`ARRAY_IN_BOUNDS` is a macro that expands to a quantified expression that expresses that the elemtns of `a->coeffs` between index values `0` and `(MLKEM_N - 1)` (inclusive) are in the range `0` through `(MLKEM_Q - 1)` (also inclusive). See the macro definition in `mlkem/cbmc.h` for details.

### Interior contracts and loop invariants

`poly_tobytes` has a single loop statement:

```
  for (int i = 0; i < MLKEM_N / 2; i++)
  { ... }
```

A candidate loop contract needs to state that:
1. The loop body assigns to variable `i` and the whole object pointed to by `r`.
2. Loop counter variable `i` is in range 0 .. MLKEM_N / 2 at the point of the loop invariant (remember the pattern above).
3. The loop terminates because the expression `MLKEM_N / 2 - i` decreases on every iteration.

Therefore, we add:

```
  for (int i = 0; i < MLKEM_N / 2; i++)
      // clang-format off
  ASSIGNS(i, OBJECT_WHOLE(r))
  INVARIANT(i >= 0)
  INVARIANT(i <= MLKEM_N / 2)
  DECREASES(MLKEM_N / 2 - i)
    // clang-format on
    { ... }
```

Note that the invariant `i >= 0` could be ommitted since `i` is of an `unsigned` integer type. It is given here for clarity only.

Another small set of changes is required to make CBMC happy with the loop body. By default, CBMC is pedantic and warns about conversions that truncate values or lose information via an implicit type conversion.

In the original version of the function, we have 3 lines, the first of which is:
```
r[3 * i + 0] = (t0 >> 0);
```
which has an implicit conversion from `uint16_t` to `uint8_t`. This is well-defined in C, but CBMC issues a warning just in case. To make CBMC happy, we have to explicitly reduce the range of t0 with a bitwise mask, and use an explicit conversion, thus:
```
r[3 * i + 0] = (uint8_t)(t0 & 0xFF);
```
and so on for the other two statements in the loop body.

### Prove it!

With those changes, CBMC completes the proof in about 10 seconds:

```
cd cbmc/proofs/poly_tobytes
make result
cat logs/result.txt
```
concludes
```
** 0 of 228 failed (1 iterations)
VERIFICATION SUCCESSFUL
```

We can also use the higher-level Python script to prove just that one function:

```
cd cbmc/proofs
MLKEM_K=3 ./run-cbmc-proofs.py --summarize -j$(nproc) -p poly_tobytes
```
yields
```
| Proof        | Status  |
|--------------|---------|
| poly_tobytes | Success |

```
