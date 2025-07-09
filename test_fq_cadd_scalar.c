#include <riscv_vector.h>
#include <stdint.h>
#include <stdio.h>

#define MLKEM_Q 3329

// Copy the fq_cadd function from rv64v_poly.c
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;
  bn = __riscv_vmslt_vx_i16m1_b16(rx, 0, vl);             /*   if x < 0:   */
  rx = __riscv_vadd_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl); /*     x += Q    */
  return rx;
}

// Test single scalar value by putting it in first position and filling rest
// with zeros
int test_scalar_value(int16_t input_val)
{
  size_t vl = __riscv_vsetvl_e16m1(16);  // Set vector length

  // Create array with test value at position 0, rest zeros
  int16_t test_array[16] = {0};
  test_array[0] = input_val;

  // Load into vector
  vint16m1_t input_vec = __riscv_vle16_v_i16m1(test_array, vl);

  // Apply fq_cadd
  vint16m1_t result_vec = fq_cadd(input_vec, vl);

  // Store result back
  int16_t results[16];
  __riscv_vse16_v_i16m1(results, result_vec, vl);

  // Calculate expected result
  int16_t expected = (input_val < 0) ? input_val + MLKEM_Q : input_val;
  int16_t actual = results[0];

  // Check correctness
  int correct = (actual == expected);

  printf("Input: %6d -> Output: %6d (Expected: %6d) %s\n", input_val, actual,
         expected, correct ? "PASS" : "FAIL");

  return correct;
}

int main()
{
  printf("Scalar test of fq_cadd function\n");
  printf("MLKEM_Q = %d\n\n", MLKEM_Q);

  // Test cases: focus on edge cases and negative values
  int16_t test_values[] = {
      // Basic cases
      0, 1, -1, -2, -3,
      // Edge cases around Q
      3328, 3329, -3329,
      // Random values
      100, -100, 1000, -1000,
      // Extreme values
      32767, -32768,
      // Values that might cause issues in Barrett reduction
      -4, -5, -10, -100};

  int num_tests = sizeof(test_values) / sizeof(test_values[0]);
  int passed = 0;

  printf("Testing %d scalar values:\n", num_tests);
  printf("----------------------------------------\n");

  for (int i = 0; i < num_tests; i++)
  {
    if (test_scalar_value(test_values[i]))
    {
      passed++;
    }
  }

  printf("----------------------------------------\n");
  printf("Results: %d/%d tests passed\n", passed, num_tests);

  if (passed == num_tests)
  {
    printf("✓ All tests PASSED! fq_cadd works correctly.\n");
    return 0;
  }
  else
  {
    printf("✗ %d tests FAILED! fq_cadd has issues.\n", num_tests - passed);
    return 1;
  }
}
