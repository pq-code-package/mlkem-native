#include <riscv_vector.h>
#include <stdint.h>
#include <stdio.h>

#define MLKEM_Q 3329
#define MLKEM_Q_HALF ((MLKEM_Q - 1) / 2)

// Copy the fq_barrett function from rv64v_poly.c
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

// Copy the fq_cadd function from rv64v_poly.c
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;
  bn = __riscv_vmslt_vx_i16m1_b16(rx, 0, vl);
  rx = __riscv_vadd_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl);
  return rx;
}

// Test single scalar value through the complete Barrett reduction pipeline
int test_barrett_pipeline(int16_t input_val)
{
  size_t vl = __riscv_vsetvl_e16m1(16);  // Set vector length

  // Create array with test value at position 0, rest zeros
  int16_t test_array[16] = {0};
  test_array[0] = input_val;

  // Load into vector
  vint16m1_t input_vec = __riscv_vle16_v_i16m1(test_array, vl);

  // Apply Barrett reduction
  vint16m1_t barrett_result = fq_barrett(input_vec, vl);

  // Store intermediate result
  int16_t barrett_output[16];
  __riscv_vse16_v_i16m1(barrett_output, barrett_result, vl);

  // Apply conditional add
  vint16m1_t final_result = fq_cadd(barrett_result, vl);

  // Store final result
  int16_t final_output[16];
  __riscv_vse16_v_i16m1(final_output, final_result, vl);

  // Calculate expected result (proper modular reduction)
  int16_t expected = ((input_val % MLKEM_Q) + MLKEM_Q) % MLKEM_Q;

  int16_t barrett_val = barrett_output[0];
  int16_t final_val = final_output[0];

  // Check if final result is in valid range [0, MLKEM_Q)
  int in_bounds = (final_val >= 0 && final_val < MLKEM_Q);
  int correct = (final_val == expected);

  printf("Input: %6d -> Barrett: %6d -> Final: %6d (Expected: %6d) %s %s\n",
         input_val, barrett_val, final_val, expected,
         in_bounds ? "IN-BOUNDS" : "OUT-OF-BOUNDS",
         correct ? "CORRECT" : "WRONG");

  return in_bounds && correct;
}

int main()
{
  printf("Scalar test of Barrett reduction pipeline (fq_barrett + fq_cadd)\n");
  printf("MLKEM_Q = %d\n\n", MLKEM_Q);

  // Test cases focusing on values that might cause issues
  int16_t test_values[] = {
      // Basic cases
      0, 1, -1, -2, -3,

      // Values around Q
      3327, 3328, 3329, 3330, 3331,

      // Values around 2*Q
      6656, 6657, 6658, 6659, 6660,

      // Negative values around -Q
      -3327, -3328, -3329, -3330, -3331,

      // Large positive values
      10000, 20000, 32767,

      // Large negative values
      -10000, -20000, -32768,

      // Values that might trigger Barrett edge cases
      // These are around the boundaries where Barrett reduction might fail
      65535, -65535, 32768, -32769};

  int num_tests = sizeof(test_values) / sizeof(test_values[0]);
  int passed = 0;
  int in_bounds_count = 0;

  printf("Testing %d values through Barrett reduction pipeline:\n", num_tests);
  printf(
      "-----------------------------------------------------------------------"
      "\n");

  for (int i = 0; i < num_tests; i++)
  {
    int result = test_barrett_pipeline(test_values[i]);
    if (result)
    {
      passed++;
    }

    // Also check if result is in bounds separately
    size_t vl = __riscv_vsetvl_e16m1(16);
    int16_t test_array[16] = {0};
    test_array[0] = test_values[i];
    vint16m1_t input_vec = __riscv_vle16_v_i16m1(test_array, vl);
    vint16m1_t barrett_result = fq_barrett(input_vec, vl);
    vint16m1_t final_result = fq_cadd(barrett_result, vl);
    int16_t final_output[16];
    __riscv_vse16_v_i16m1(final_output, final_result, vl);

    if (final_output[0] >= 0 && final_output[0] < MLKEM_Q)
    {
      in_bounds_count++;
    }
  }

  printf(
      "-----------------------------------------------------------------------"
      "\n");
  printf("Results: %d/%d tests passed (correct value)\n", passed, num_tests);
  printf("         %d/%d results in bounds [0, %d)\n", in_bounds_count,
         num_tests, MLKEM_Q);

  if (in_bounds_count == num_tests)
  {
    printf("✓ All results are IN BOUNDS! Barrett pipeline works for bounds.\n");
  }
  else
  {
    printf("✗ %d results are OUT OF BOUNDS! Barrett pipeline has issues.\n",
           num_tests - in_bounds_count);
  }

  if (passed == num_tests)
  {
    printf("✓ All results are CORRECT! Barrett pipeline works perfectly.\n");
    return 0;
  }
  else
  {
    printf("✗ %d results are WRONG! Barrett pipeline has correctness issues.\n",
           num_tests - passed);
    return 1;
  }
}
