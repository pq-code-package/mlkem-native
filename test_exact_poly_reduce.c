#include <riscv_vector.h>
#include <stdint.h>
#include <stdio.h>

// Exact constants from mlkem-native
#define MLKEM_Q 3329
#define MLKEM_N 256
#define MLKEM_Q_HALF ((MLKEM_Q - 1) / 2)

// Exact vector length definition from mlkem-native
#define MLK_RVV_VLEN 256
#define MLK_RVV_E16M1_VL (MLK_RVV_VLEN / 16)

// Function prototypes
static inline vint16m1_t fq_barrett(vint16m1_t a, size_t vl);
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl);
void mlk_rv64v_poly_reduce(int16_t *r);  // EXACT function from mlkem-native
static int test_scalar_poly_reduce(int16_t input_val);

// EXACT fq_barrett function from mlkem-native (without debug assertions)
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

// EXACT fq_cadd function from mlkem-native
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;

  bn = __riscv_vmslt_vx_i16m1_b16(rx, 0, vl);             /*   if x < 0:   */
  rx = __riscv_vadd_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl); /*     x += Q    */

  return rx;
}

// EXACT mlk_rv64v_poly_reduce function from mlkem-native (NO INSTRUMENTATION)
void mlk_rv64v_poly_reduce(int16_t *r)
{
  size_t vl = MLK_RVV_E16M1_VL;
  vint16m1_t vt;

  for (size_t i = 0; i < MLKEM_N; i += vl)
  {
    vt = __riscv_vle16_v_i16m1(&r[i], vl);
    vt = fq_barrett(vt, vl);
    vt = fq_cadd(vt, vl);
    __riscv_vse16_v_i16m1(&r[i], vt, vl);
  }
}

// Test single scalar value by putting it in first position, rest zeros
static int test_scalar_poly_reduce(int16_t input_val)
{
  // Create polynomial buffer with test value at position 0, rest zeros
  int16_t poly[MLKEM_N] = {0};
  poly[0] = input_val;

  // Apply EXACT mlk_rv64v_poly_reduce function
  mlk_rv64v_poly_reduce(poly);

  // Get result from first position
  int16_t output_val = poly[0];

  // Calculate expected result
  int16_t expected = ((input_val % MLKEM_Q) + MLKEM_Q) % MLKEM_Q;

  // Check correctness and bounds
  int in_bounds = (output_val >= 0 && output_val < MLKEM_Q);
  int correct = (output_val == expected);

  printf("Input: %6d -> Output: %6d (Expected: %6d) %s %s\n", input_val,
         output_val, expected, in_bounds ? "IN-BOUNDS" : "OUT-OF-BOUNDS",
         correct ? "CORRECT" : "WRONG");

  return in_bounds && correct;
}

int main(void)
{
  printf("EXACT mlkem-native poly_reduce test (scalar conversion)\n");
  printf("MLKEM_Q = %d, MLKEM_N = %d\n", MLKEM_Q, MLKEM_N);
  printf("Vector length: %d elements\n", MLK_RVV_E16M1_VL);

  // Test cases: focus on values that caused issues in the original ML-KEM tests
  int16_t test_values[] = {
      // Basic cases
      0, 1, -1, -2, -3,

      // Values that were producing -1, -2 in the original tests
      3328, 3329, 6657, 6658,

      // Values around Q boundaries
      3327, 3330, 6656, 6659, 6660,

      // Negative values around -Q
      -3327, -3328, -3329, -3330, -3331,

      // Large values that might cause Barrett edge cases
      10000, 20000, 32767, -10000, -20000, -32768,

      // Edge cases
      65535, -65535};

  int num_tests = sizeof(test_values) / sizeof(test_values[0]);
  int passed = 0;
  int in_bounds_count = 0;

  printf("\nTesting %d scalar values through EXACT mlkem-native poly_reduce:\n",
         num_tests);
  printf("----------------------------------------------------------------\n");

  for (int i = 0; i < num_tests; i++)
  {
    int result = test_scalar_poly_reduce(test_values[i]);
    if (result)
    {
      passed++;
    }

    // Also count in-bounds separately
    int16_t poly[MLKEM_N] = {0};
    poly[0] = test_values[i];
    mlk_rv64v_poly_reduce(poly);
    if (poly[0] >= 0 && poly[0] < MLKEM_Q)
    {
      in_bounds_count++;
    }
  }

  printf("----------------------------------------------------------------\n");
  printf("Results: %d/%d tests passed (correct value)\n", passed, num_tests);
  printf("         %d/%d results in bounds [0, %d)\n", in_bounds_count,
         num_tests, MLKEM_Q);

  if (in_bounds_count == num_tests)
  {
    printf(
        "✓ All results are IN BOUNDS! EXACT poly_reduce works for bounds.\n");
  }
  else
  {
    printf(
        "✗ %d results are OUT OF BOUNDS! EXACT poly_reduce has bounds "
        "issues.\n",
        num_tests - in_bounds_count);
  }

  if (passed == num_tests)
  {
    printf("✓ All results are CORRECT! EXACT poly_reduce works perfectly.\n");
    return 0;
  }
  else
  {
    printf(
        "✗ %d results are WRONG! EXACT poly_reduce has correctness issues.\n",
        num_tests - passed);
    return 1;
  }
}
