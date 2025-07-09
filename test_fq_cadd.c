#include <riscv_vector.h>
#include <stdint.h>
#include <stdio.h>

#define MLKEM_Q 3329
#define MLKEM_N 256

// Copy the fq_cadd function from rv64v_poly.c
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;
  bn = __riscv_vmslt_vx_i16m1_b16(rx, 0, vl);             /*   if x < 0:   */
  rx = __riscv_vadd_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl); /*     x += Q    */
  return rx;
}

int main()
{
  printf("Testing fq_cadd function\n");
  printf("MLKEM_Q = %d\n\n", MLKEM_Q);

  // Test cases: mix of positive, negative, and edge case values
  int16_t test_input[] = {
      0,     1,   -1,   -2,   -3,    3328,  3329,
      -3329, 100, -100, 1000, -1000, 32767, -32768  // int16_t limits
  };

  int num_tests = sizeof(test_input) / sizeof(test_input[0]);
  size_t vl = __riscv_vsetvl_e16m1(num_tests);

  printf("Vector length: %zu\n", vl);
  printf("Number of test values: %d\n\n", num_tests);

  // Load test values into vector
  vint16m1_t input_vec = __riscv_vle16_v_i16m1(test_input, vl);

  // Apply fq_cadd
  vint16m1_t result_vec = fq_cadd(input_vec, vl);

  // Store results back to array
  int16_t results[16];
  __riscv_vse16_v_i16m1(results, result_vec, vl);

  // Print results
  printf("Input\t-> Output\tExpected\tStatus\n");
  printf("-----\t   ------\t--------\t------\n");

  int failures = 0;
  for (int i = 0; i < num_tests; i++)
  {
    int16_t input = test_input[i];
    int16_t output = results[i];
    int16_t expected;

    // Calculate expected result
    if (input < 0)
    {
      expected = input + MLKEM_Q;
    }
    else
    {
      expected = input;
    }

    // Check if result is correct
    int correct = (output == expected);
    if (!correct)
    {
      failures++;
    }

    printf("%6d\t-> %6d\t%8d\t%s\n", input, output, expected,
           correct ? "PASS" : "FAIL");
  }

  printf("\n");
  if (failures == 0)
  {
    printf("✓ All tests PASSED!\n");
    return 0;
  }
  else
  {
    printf("✗ %d tests FAILED!\n", failures);
    return 1;
  }
}
