#include <riscv_vector.h>
#include <stdint.h>
#include <stdio.h>

#define MLKEM_Q 3329
#define MLKEM_N 256

// Set vector length to match actual implementation (256-bit vectors)
#define MLK_RVV_E16M1_VL (__riscv_vsetvlmax_e16m1())

// Function prototypes
static inline vint16m1_t fq_barrett(vint16m1_t a, size_t vl);
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl);
static void poly_reduce_256bit(int16_t *r);
static int test_poly_reduce_256bit_bounds(int16_t *test_values, int num_values,
                                          const char *test_name);

// Barrett reduction function (matches rv64v_poly.c exactly)
static inline vint16m1_t fq_barrett(vint16m1_t a, size_t vl)
{
  vint16m1_t t;
  const int16_t v = ((1 << 26) + MLKEM_Q / 2) / MLKEM_Q;

  t = __riscv_vmulh_vx_i16m1(a, v, vl);
  t = __riscv_vadd_vx_i16m1(t, 1 << (25 - 16), vl);
  t = __riscv_vsra_vx_i16m1(t, 26 - 16, vl);
  t = __riscv_vmul_vx_i16m1(t, MLKEM_Q, vl);
  t = __riscv_vsub_vv_i16m1(a, t, vl);

  return t;
}

// Conditional add function (matches rv64v_poly.c exactly)
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;
  bn = __riscv_vmslt_vx_i16m1_b16(rx, 0, vl);
  rx = __riscv_vadd_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl);
  return rx;
}

// Standalone poly_reduce function using 256-bit vectors (matches ML-KEM
// exactly)
static void poly_reduce_256bit(int16_t *r)
{
  size_t vl = MLK_RVV_E16M1_VL;  // Use maximum vector length (256-bit)
  vint16m1_t vt;

  printf("[DEBUG] Vector length: %zu elements\n", vl);
  printf("[DEBUG] Processing %d coefficients in chunks of %zu\n", MLKEM_N, vl);

  for (size_t i = 0; i < MLKEM_N; i += vl)
  {
    printf("[DEBUG] Processing chunk starting at index %zu\n", i);

    // Store input values for this chunk
    printf("[DEBUG] Input values: ");
    for (size_t j = 0; j < vl && (i + j) < MLKEM_N; j++)
    {
      printf("%d ", r[i + j]);
    }
    printf("\n");

    vt = __riscv_vle16_v_i16m1(&r[i], vl);
    vt = fq_barrett(vt, vl);
    vt = fq_cadd(vt, vl);
    __riscv_vse16_v_i16m1(&r[i], vt, vl);

    // Check output values for this chunk
    printf("[DEBUG] Output values: ");
    int out_of_bounds_in_chunk = 0;
    for (size_t j = 0; j < vl && (i + j) < MLKEM_N; j++)
    {
      printf("%d ", r[i + j]);
      if (r[i + j] < 0 || r[i + j] >= MLKEM_Q)
      {
        out_of_bounds_in_chunk++;
        printf("(OOB!) ");
      }
    }
    printf("\n");

    if (out_of_bounds_in_chunk > 0)
    {
      printf("[ERROR] %d out-of-bounds values in this chunk!\n",
             out_of_bounds_in_chunk);
    }
    printf("\n");
  }
}

// Test function that checks bounds after poly_reduce with 256-bit vectors
static int test_poly_reduce_256bit_bounds(int16_t *test_values, int num_values,
                                          const char *test_name)
{
  printf("\n========================================\n");
  printf("Testing %s (%d values) with 256-bit vectors:\n", test_name,
         num_values);
  printf("========================================\n");

  // Create a polynomial array and fill with test values
  int16_t poly[MLKEM_N] = {0};

  // Copy test values to beginning of polynomial
  for (int i = 0; i < num_values && i < MLKEM_N; i++)
  {
    poly[i] = test_values[i];
  }

  printf("First 20 input values: ");
  for (int i = 0; i < 20 && i < num_values; i++)
  {
    printf("%d ", poly[i]);
  }
  printf("\n\n");

  // Apply poly_reduce with 256-bit vectors
  poly_reduce_256bit(poly);

  printf("First 20 output values: ");
  for (int i = 0; i < 20 && i < num_values; i++)
  {
    printf("%d ", poly[i]);
  }
  printf("\n");

  // Check bounds and correctness for all values
  int out_of_bounds = 0;
  int incorrect = 0;

  for (int i = 0; i < num_values; i++)
  {
    int16_t input = test_values[i];
    int16_t output = poly[i];
    int16_t expected = ((input % MLKEM_Q) + MLKEM_Q) % MLKEM_Q;

    if (output < 0 || output >= MLKEM_Q)
    {
      out_of_bounds++;
      printf("OUT-OF-BOUNDS at index %d: input=%d, output=%d\n", i, input,
             output);
    }

    if (output != expected)
    {
      incorrect++;
      printf("INCORRECT at index %d: input=%d, output=%d, expected=%d\n", i,
             input, output, expected);
    }
  }

  printf("\nFinal Results: %d out-of-bounds, %d incorrect out of %d values\n",
         out_of_bounds, incorrect, num_values);

  return (out_of_bounds == 0 && incorrect == 0);
}

int main(void)
{
  printf(
      "256-bit Vector poly_reduce test with CI CFLAGS (matches actual ML-KEM "
      "implementation)\n");
  printf("MLKEM_Q = %d, MLKEM_N = %d\n", MLKEM_Q, MLKEM_N);

  // Check actual vector length
  size_t actual_vl = MLK_RVV_E16M1_VL;
  printf(
      "Actual vector length: %zu elements (should be 16 for 256-bit vectors)\n",
      actual_vl);
  printf("Vector width: %zu bits\n", actual_vl * 16);

  int total_tests = 0;
  int passed_tests = 0;

  // Test 1: Values that caused issues in the original ML-KEM tests
  int16_t problematic[] = {
      // Values that were producing -1, -2 in the original tests
      3328, 3329, 6657, 6658, -1, -2, -3,
      // Values around boundaries
      0, 1, 3327, 3330, 6656, 6659, 6660};
  if (test_poly_reduce_256bit_bounds(problematic, 14,
                                     "Problematic values from ML-KEM"))
  {
    passed_tests++;
  }
  total_tests++;

  // Test 2: Full polynomial with edge case values
  int16_t full_poly[MLKEM_N];
  for (int i = 0; i < MLKEM_N; i++)
  {
    // Fill with values that might cause Barrett reduction edge cases
    if (i < 16)
    {
      // First vector: known problematic values
      int16_t problem_vals[] = {-1,    -2, 3328,  3329,   6657,  6658,
                                -3329, 0,  32767, -32768, 10000, -10000,
                                1,     -3, 3327,  6659};
      full_poly[i] = problem_vals[i];
    }
    else
    {
      // Rest: pseudo-random values that might appear in ML-KEM
      full_poly[i] = (int16_t)((i * 1337 + 42) % 20000 - 10000);
    }
  }
  if (test_poly_reduce_256bit_bounds(full_poly, MLKEM_N,
                                     "Full polynomial with edge cases"))
  {
    passed_tests++;
  }
  total_tests++;

  printf("\n========================================\n");
  printf("Overall Results: %d/%d test groups passed\n", passed_tests,
         total_tests);

  if (passed_tests == total_tests)
  {
    printf(
        "✓ All tests PASSED! 256-bit vector poly_reduce works correctly with "
        "CI CFLAGS.\n");
    return 0;
  }
  else
  {
    printf(
        "✗ %d test groups FAILED! 256-bit vector poly_reduce has issues with "
        "CI CFLAGS.\n",
        total_tests - passed_tests);
    return 1;
  }
}
