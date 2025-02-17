[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# CBMC Proof Guide and Cookbook for mlkem-native

This document acts as a guide to how we develop proofs of mlkem-native's C code using
[CBMC](https://model-checking.github.io/cbmc-training/). It concentrates on the use of _contracts_ to achieve
_unbounded_ and _modular_ proofs of type-safety and correctness properties.

## Scope

Our CBMC proofs confirm the absence of certain classes of undefined behaviour, such as integer overflow or out of bounds
memory accesses -- for the precise list of conditions checked, see the CBMC configuration in
[Makefile.common](Makefile.common). For many arithmetic functions, we additionally specify how they affect coefficient
bounds: For example, we show that the result of `poly_invntt_tomont()` has coefficients bound by
`MLK_INVNTT_BOUND`. Finally, some simple functions have their full functional behaviour specified: For example, the
specification of the constant-time `ct_memcmp()` shows that, functionally, it is just an ordinary `memcmp()`.

## CBMC annotations

CBMC proofs are largely automatic; there are no proof scripts as in interactive theorem proving. Instead, CBMC consumes
_annotated_ C code and checks that it does not exhibit the configured classes of undefined behaviour within the
context described by the annotations; if the annotations add further constraints, those are checked, too. For example, a
function contract annotation provides contextual assumptions about a function as _preconditions_ to CBMC, and adds
further _constraints_ for the program state at function return.

In mlkem-native, we use abbreviated forms of the CBMC annotations defined by macros in the [cbmc.h](../../mlkem/cbmc.h). We
now list the most prominent.

### Function contracts

A _function contract_ can be added where a function is declared. For `static` functions where the sites of
declaration and definition coincide, it is part of the definition. mlkem-native's syntax for function contracts is

```c
int foo(args...)
__contract(
  requires(...)
  ...
  requires(...)
  assigns(...)
  ensures(...)
  ...
  ensures(...)
);
```

Here, an arbitrary number of `requires` clauses can be used to specify assumptions made by the function, and an
arbitrary number of `ensures(...)` clauses specifies the post-condition. One also needs an `assigns(...)` clause
indicating the 'footprint' of the function, that is, the objects it changes.

### Pointer validity

When dealing with pointers, a very common precondition to encounter is `memory_no_alias(ptr, len)`. This asserts that
`ptr` is a valid pointer to a block of memory of length `len` bytes, that does not overlap with other memory regions
also described via `memory_no_alias(...)`. Hence, a function operating on `n` memory buffers will typically have `n`
instances of `memory_no_alias(...)` in its precondition.

Care has to be taken for functions where aliasing is needed. Aliasing constraints can be difficult to specify, and we
reduce it as much as possible in mlkem-native. For example, rather than having `poly_add(dst, src0, src1)` where `dst`
may overlap with `src0` or `src1`, we only have a destructive `poly_add(dst, src)` implementing `dst += src`, thereby
avoiding the need to specify an aliasing constraint.

Care also has to be taken when _invoking_ a function that has a contract with multiple `memory_no_alias(...)` clauses;
Here, CBMC will assert that the pointer arguments point to different C objects, rather than conducting a fine-grained
check of disjointness. This simplifies the constraints, but can be impeding for the user: For example, given `foo x[2]`
for some struct `foo`, you cannot pass `&foo[0]`, `&foo[1]` as arguments to a function specified using
`memory_no_alias(...)` for both, because `&foo[0]`, `&foo[1]` point to the same object. In mlkem-native, we sometimes
work around this by manually splitting statically-sized arrays into multiple separate objects.

### Memory footprint

The most common way to specify memory footprint in `assigns(...)` clauses is via `memory_slice(ptr, len)`. This asserts
that the code in question may change the first `len` bytes starting from `ptr`.

There is also `object_whole(ptr)`, which more coarsely asserts that the entire object can change. This has to be used
with care: If a function precondition specifies `requires(memory_no_alias(ptr, 42))` and `assigns(object_whole(ptr))`
and is called in a context where `ptr` is, say, a slice of some larger structure, then the entire structure will be
marked as tainted by the function call. This is often not desired, hence the more fine-grained `memory_slice(...)` is
desirable.

### Quantifiers and bounds

If you need to specify a quantified condition for use in `ensures(...)` or `requires(...)`, you can use the
`forall(...)` wrapper. It has the shape `forall(k, low_bound, high_bound, condition)`, where `k` is a name for the
quantified variable `[low_bound, ..., high_bound-1]` the quantification range, and `condition` is the quantified
condition (usually depending on `k`).

A prominent condition built from `forall` are `array_bound`:
`array_bound(arr, idx_low, idx_high, value_low, value_high)` asserts that the values of the array `arr` within
`[idx_low, ..., idx_high - 1]` are within the range `[value_low, ..., value_high]`. There is also `array_abs_bound(...)`
for absolute value constraints.

### Loop invariants

Loop invariants are specified using `__loop__(...)` as follows:

```c
for (...)
__loop__(
  assigns(...)
  invariant(...)
  ...
  invariant(...))
{
   ...
}
```

Here, one or more `invariant(...)` clauses describe the invariant maintained by the loop body. As for function
contracts, `assigns(...)` captures the footprint of the loop body.

## Common Patterns

### `for` loops

The most common, and easiest, pattern is a "for" loop that has a counter starting at 0, and counting up to some upper bound, like this:

```
unsigned i;
for (i = 0; i < C; i++) {
    S;
}
```

CBMC requires basic assigns, loop-invariant, and optionally a decreases contracts _in exactly that order_. The most
common pattern is:

```
unsigned i;
for (i = 0; i < C; i++)
__loop__(
  assigns(i, ...)   /* plus whatever else S does */
  invariant(i <= C) /* Counter invariant */
  invariant(...)    /* Further invariants */
  decreases(C - i))
{
    S;
}
```

Importantly, the `i <= C` in the invariant is _not_ a typo: CBMC places the invariant just _after_ the loop counter has
been incremented, but just _before_ the loop exit test, so it is possible for `i == C` at the invariant on the final
iteration of the loop.

### Iterating over an array for a `for` loop

A common pattern is doing something to every element of an array. An example would be setting every element of a
byte-array to 0x00 given a pointer to the first element and a length. Initially, we want to prove type safety of this
function, so we won't even bother with a post-condition. The function specification might look like this:

```
void zero_array_ts (uint8_t *dst, int len)
__contract__(
  requires(memory_no_alias(dst, len))
  assigns(object_whole(dst)));
```

As mentioned before, the `memory_no_alias(dst,len)` in the precondition means that the pointer value `dst` is not `NULL`
and is pointing to at least `len` bytes of data. The `assigns` contract (in this case) means that when the function
returns, it promises to have updated the whole object pointed to by dst - in this case `len` bytes of data.

The body:

```
void zero_array_ts (uint8_t *dst, int len)
{
    unsigned i;
    for (i = 0; i < len; i++)
    __loop__(
      assigns(i, object_whole(dst))
      invariant(i <= len)
      decreases(len - i))
    {
        dst[i] = 0;
    }
}
```

For memory safety, the only interesting proof obligation for CBMC here is that the assignment `dst[i]` is valid. This
requires a proof that `i < len` which is trivially discharged given the loop invariant `i <= len`, plus the fact that
the loop has not terminated, and hence `i < len`.

### Correctness proof of zero_array

We can go further, and prove the correctness of that function by adding a post-condition, and extending the loop
invariant, as follows:

```
void zero_array_correct (uint8_t *dst, int len)
__contract__(
  requires(memory_no_alias(dst, len))
  assigns(object_whole(dst))
  ensures(forall(k, 0, len, dst[k] == 0)));
```

The body is the same, but now with a stronger loop invariant. The invariant says that "after j loop iterations, we've
zeroed the first j elements of the array", so:

```
void zero_array_correct (uint8_t *dst, int len)
{
    unsigned i;
    for (i = 0; i < len; i++)
    __loop__(
      assigns(i, object_whole(dst))
      invariant(i <= len)
      invariant(forall(j, 0, i, dst[j] == 0))
      decreases(len - i))
    {
        dst[i] = 0;
    }
}
```

Things to note:
1. The type of the quantified variable is `unsigned`.
2. Don't overload your program variables with quantified variables inside your forall contracts. It get confusing if you
   do.

Note that the invariant `invariant(forall(j, 0, i, dst[j] == 0))` is vacuous at loop entry, where `i == 0` and the
premise `j < i` of the bounded quantification in `forall(...)` is therefore unsatisfiable (remember that `i,j` are
`unsigned`). This pattern comes up frequently when one reasons about slices of arrays, and one or more of the slices has
a "null range" at either the loop entry or exit, and therefore that particular quantified constraint is vacuously
true.

## Invariant && loop-exit ==> post-condition

When the loop completes, CBMC reasons about the following code (if any) based on the combination of (a) loop invariant,
and (b) loop exit condition. In the simplest case where there is no code following the loop, this means that the loop
invariant and exit condition together should imply the function's post-condition.

For the example above, we need to prove:

```
// Loop invariant
(i <= len && forall(j, 0, j < i, dst[j] == 0))
&&
// Loop exit condition must be TRUE, so
i == len)

===>

// Post-condition
forall(k, 0, len, dst[k] == 0)
```

which holds by rewriting `i` by `len` in the loop invariant.

## Recipe to prove a new function

If you want to develop a proof of a function, here are the basic steps.
1. Populate a proof directory
2. Update Makefile
3. Update harness function
4. Supply top-level contracts for the function
5. Supply loop-invariants (if required) and other interior contracts
6. Prove it!

These steps are expanded on in the following sub-sections.

### Populate a proof directory

For mlkem-native, proof directories lie below `cbmc`.

Create a new sub-directory in there, where the name of the directory is the name of the function. You don't need a
namespacing prefix.

That directory needs to contain 3 files.

* cbmc-proof.txt
* Makefile
* XXX_harness.c

where "XXX" is the name of the function being proved - same as the directory name.

We suggest that you copy these files from an existing proof directory and modify the latter two. The `cbmc-proof.txt`
file is just a marker that says "this directory contains a CBMC proof" to the tools, so no modification is required.

### Update Makefile

The `Makefile` sets options and targets for this proof. Let's imagine that the function we want to prove is called `XXX`
(without namespacing prefix).

Edit the Makefile and update the definition of the following variables:

* HARNESS_FILE - should be `XXX_harness`
* PROOF_UID - should be `XXX`
* PROJECT_SOURCES - should the files containing the source code of XXX
* CHECK_FUNCTION_CONTRACTS - set to the `XXX`, but including the `$(MLK_NAMESPACE)` prefix if required
* USE_FUNCTION_CONTRACTS - a list of functions that `XXX` calls where you want CBMC to use the contracts of the called
  function for proof, rather than 'inlining' the called function for proof. Include the `$(MLK_NAMESPACE)` prefix if
  required
* EXTERNAL_SAT_SOLVER - should _always_ be "nothing" to prevent CBMC selecting a SAT backend over the selected SMT backend.
* CBMCFLAGS - additional flags to pass to the final run of CBMC. This is normally set to `--smt2` which tells cbmc to
  run Z3 as its underlying solver. Can also be set to `--bitwuzla` which is sometimes better at generating
  counter-examples when Z3 fails.
* FUNCTION_NAME - set to `XXX` with the `$(MLK_NAMESPACE)` prefix if required
* CBMC_OBJECT_BITS. Normally set to 8, but might need to be increased if CBMC runs out of memory for this proof.

For documentation of these (and the other) options, see the [cbmc/Makefile.common](Makefile.common) file.

The `USE_FUNCTION_CONTRACTS` option should be used where possible, since contracts enable modular proof, which is far more efficient
 than inlining, which tends to explode in complexity for higher-level functions.

#### Z3 or Bitwuzla?

We have found that it's better to use Bitwuzla in the initial stages of developing and debugging a new proof.

When Z3 finds that a proof is "sat" (i.e. not true), it tries to produce a counter-example to show you what's
wrong. Unfortunately, recent versions of Z3 can produce quantified expressions as output that cannot be currently
understood by CBMC. This leads CBMC to fail with an error such as

```
SMT2 solver returned non-constant value for variable Bxxx
```

This is not helpful when trying to understand a failed proof. Bitwuzla works better and produces reliable counter-examples.

Once a proof is working OK, you may revert to Z3 to check if it _also_ passes with Z3, and perhaps faster. If it does,
then keep Z3 as the selected prover. If not, then stick with Bitwuzla.

### Update harness function

The file `XXX_harness.c` should declare a single function called `XXX_harness()` that calls `XXX` exactly once, with
appropriately typed actual parameters. The actual parameters should be variables of the simplest type possible, and
should be _uninitialized_. Where a pointer value is required, create an uninitialized variable of that pointer type. Do
_not_ pass the address of a stack-allocated object.

For example, if a function f() expects a single parameter which is a pointer to some struct s:
```
void f(s *x)
requires(memory_no_alias(x, sizeof(s));
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

Using contracts, this harness function should not need to contain any CBMC `assume` or `assert` statements at all.

### Supply top-level contracts

Add a `__contract(...)__` contract in the header defining the function-under-proof. If the function is `static`, add the
`__contract__(...)` in the `.c` file at point of definition. As mentioned before, the pattern is as follows:

```c
return_type function_name(arg0, arg1, ...)
__contract__(
  requires()
  assigns()
  ensures());
```

or

```c
return_type function_name(arg0, arg1, ...)
__contract__(
  requires()
  assigns()
  ensures())
{
   ...
}
```

Note that when added to a declaration, the contract has to come before the final semicolon concluding the declaration.

### Interior contracts and loop invariants

If XXX contains no loop statements, then you might be able to just skip this step. Otherwise, add `__loop__(...)`
annotations to every loop in the function under proof.

### Prove it!

Proof of a single function can be run from the proof directory for that function with `make result`.

This produces `logs/result.txt` in plaintext format.

Before pushing a new proof for a new function, make sure that _all_ proofs run OK from the [proofs/cbmc](./) directory with

```
MLKEM_K=3 ./run-cbmc-proofs.py --summarize -j$(nproc)
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

The proof directory is [proofs/cbmc/poly_tobytes](poly_tobytes).

### Update Makefile

The significant changes are:
```
HARNESS_FILE = poly_tobytes_harness
PROOF_UID = poly_tobytes
PROJECT_SOURCES += $(SRCDIR)/mlkem/poly.c
CHECK_FUNCTION_CONTRACTS=$(MLK_NAMESPACE)poly_tobytes
USE_FUNCTION_CONTRACTS=
FUNCTION_NAME = $(MLK_NAMESPACE)poly_tobytes
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
So we need to write a requires contract to constrain the ranges of the coefficients denoted by the parameter `a`. There
is no constraint on the output byte array, other than it must be the right length, which is given by the function
prototype.

We can use the macros in [mlkem/cbmc.h](../../mlkem/cbmc.h) to help, thus:

```
void poly_tobytes(uint8_t r[MLKEM_POLYBYTES], const poly *a)
__contract__(
  requires(memory_no_alias(a, sizeof(poly)))
  requires(array_bound(a->coeffs, 0, MLKEM_N, 0, (MLKEM_Q - 1)))
  assigns(object_whole(r)));
```

`array_bound` is a macro that expands to a quantified expression that expresses that the elemtns of `a->coeffs` between
index values `0` (inclusive) and `MLKEM_N` (exclusive) are in the range `0` through `(MLKEM_Q - 1)` (both
inclusive). See the macro definition in [mlkem/cbmc.h](../../mlkem/cbmc.h) for details.

### Interior contracts and loop invariants

`poly_tobytes` has a single loop statement:

```
  unsigned i;
  for (i = 0; i < MLKEM_N / 2; i++)
  { ... }
```

A candidate loop contract needs to state that:
1. The loop body assigns to variable `i` and the whole object pointed to by `r`.
2. Loop counter variable `i` is in range `0 .. MLKEM_N / 2` at the point of the loop invariant (remember the pattern above).
3. The loop terminates because the expression `MLKEM_N / 2 - i` decreases on every iteration.

Therefore, we add:

```
  unsigned i;
  for (i = 0; i < MLKEM_N / 2; i++)
  __loop__(
    assigns(i, object_whole(r))
    invariant(i <= MLKEM_N / 2)
    decreases(MLKEM_N / 2 - i))
  { ... }
```

Another small set of changes is required to make CBMC happy with the loop body. By default, CBMC is pedantic and warns
about conversions that truncate values or lose information via an implicit type conversion.

In the original version of the function, we have 3 lines, the first of which is:
```
r[3 * i + 0] = (t0 >> 0);
```
which has an implicit conversion from `uint16_t` to `uint8_t`. This is well-defined in C, but CBMC issues a warning just
in case. To make CBMC happy, we have to explicitly reduce the range of t0 with a bitwise mask, and use an explicit
conversion, thus:
```
r[3 * i + 0] = (uint8_t)(t0 & 0xFF);
```
and so on for the other two statements in the loop body.

### Prove it!

With those changes, CBMC completes the proof in about 10 seconds:

```
cd proofs/cbmc/poly_tobytes
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
cd proofs/cbmc
MLKEM_K=3 ./run-cbmc-proofs.py --summarize -j$(nproc) -p poly_tobytes
```
yields
```
| Proof        | Status  |
|--------------|---------|
| poly_tobytes | Success |

```
