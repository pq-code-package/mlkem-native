// SPDX-License-Identifier: Apache-2.0

///////////////////////////////////////////////////
// Basic replacements for __CPROVER_XXX contracts
///////////////////////////////////////////////////

#ifndef CBMC

#define STATIC_TESTABLE static
#define STATIC_INLINE_TESTABLE static inline

// CBMC top-level contracts are replaced by "" for compilation
#define ASSIGNS(...)
#define REQUIRES(...)
#define ENSURES(...)
#define DECREASES(...)
#define INVARIANT(...)
#define ASSERT(...)
#define ASSUME(...)

#else  // CBMC _is_ defined, therefore we're doing proof

// expose certain procedures to CBMC proofs that are static otherwise
#define STATIC_TESTABLE
#define STATIC_INLINE_TESTABLE


// https://diffblue.github.io/cbmc/contracts-assigns.html
#define ASSIGNS(...) __CPROVER_assigns(__VA_ARGS__)

// https://diffblue.github.io/cbmc/contracts-requires-ensures.html
#define REQUIRES(...) __CPROVER_requires(__VA_ARGS__)
#define ENSURES(...) __CPROVER_ensures(__VA_ARGS__)

// note we drop "loop_" here since there are no other kind of invariants
// in CBMC. An "invariant" is _always_ a "loop invariant" so no need to
// keep that qualification
// https://diffblue.github.io/cbmc/contracts-loops.html
#define INVARIANT(...) __CPROVER_loop_invariant(__VA_ARGS__)
#define DECREASES(...) __CPROVER_decreases(__VA_ARGS__)

#define ASSERT(...) __CPROVER_assert(__VA_ARGS__)
#define ASSUME(...) __CPROVER_assume(__VA_ARGS__)

#define READABLE(...) __CPROVER_r_ok(__VA_ARGS__)
#define WRITEABLE(...) __CPROVER_w_ok(__VA_ARGS__)

///////////////////////////////////////////////////
// Macros for "expression" forms that may appear
// _inside_ top-level contracts.
///////////////////////////////////////////////////

// function return value - useful inside ENSURES
// https://diffblue.github.io/cbmc/contracts-functions.html
#define RETURN_VALUE (__CPROVER_return_value)

// ASSIGNS l-value targets
// https://diffblue.github.io/cbmc/contracts-assigns.html
#define TYPED_TARGET(...) __CPROVER_typed_target(__VA_ARGS__)
#define OBJECT_WHOLE(...) __CPROVER_object_whole(__VA_ARGS__)
#define OBJECT_FROM(...) __CPROVER_object_from(__VA_ARGS__)
#define OBJECT_UPTO(...) __CPROVER_object_upto(__VA_ARGS__)

#define SAME_OBJECT(...) __CPROVER_same_object(__VA_ARGS__)

// Pointer-related predicates
// https://diffblue.github.io/cbmc/contracts-memory-predicates.html
#define IS_FRESH(...) __CPROVER_is_fresh(__VA_ARGS__)
#define POINTER_IN_RANGE(...) __CPROVER_pointer_in_range_dfcc(__VA_ARGS__)
#define READABLE(...) __CPROVER_r_ok(__VA_ARGS__)
#define WRITEABLE(...) __CPROVER_w_ok(__VA_ARGS__)

// Function pointer/contract establishment
// https://diffblue.github.io/cbmc/contracts-function-pointer-predicates.html
#define OBEYS_CONTRACT(...) __CPROVER_obeys_contract(__VA_ARGS__)

// History variables
// https://diffblue.github.io/cbmc/contracts-history-variables.html
#define OLD(...) __CPROVER_old(__VA_ARGS__)
#define LOOP_ENTRY(...) __CPROVER_loop_entry(__VA_ARGS__)

// Quantifiers
// Note that the range on qvar is _inclusive_ between qvar_lb .. qvar_ub
// https://diffblue.github.io/cbmc/contracts-quantifiers.html

// Prevent clang-format from corrupting CBMC's special ==> operator
// clang-format off
#define FORALL(type, qvar, qvar_lb, qvar_ub, predicate)          \
  __CPROVER_forall                                               \
  {                                                              \
    type qvar;                                                   \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) ==> (predicate) \
  }
// clang-format on

#define EXISTS(type, qvar, qvar_lb, qvar_ub, predicate)         \
  __CPROVER_exists {                                            \
    type qvar;                                                  \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) && (predicate) \
  }

///////////////////////////////////////////////////
// Convenience macros for common contract patterns
///////////////////////////////////////////////////

// Boolean-value predidate that asserts that "all values of array_var are in
// range value_lb .. value_ub (inclusive)"
//
// Example:
//  ARRAY_IN_BOUNDS(unsigned, k, 0, MLKEM_N-1, a->coeffs, -(MLKEM_Q - 1),
//  MLKEM_Q - 1)
// expands to
//  __CPROVER_forall { unsigned k; (0 <= k && k <= MLKEM_N-1) ==> ( (-(MLKEM_Q -
//  1) <= a->coeffs[k]) && (a->coeffs[k] <= (MLKEM_Q - 1))) }

// Prevent clang-format from corrupting CBMC's special ==> operator
// clang-format off
#define ARRAY_IN_BOUNDS(indextype, qvar, qvar_lb, qvar_ub, array_var, \
                        value_lb, value_ub)                           \
  __CPROVER_forall                                                    \
  {                                                                   \
    indextype qvar;                                                   \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) ==>                  \
          (((value_lb) <= (array_var[(qvar)])) &&                     \
           ((array_var[(qvar)]) <= (value_ub)))                       \
  }
// clang-format on

#endif
