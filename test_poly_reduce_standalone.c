#include <riscv_vector.h>
#include <stdint.h>
#include <stdio.h>

#define MLKEM_Q 3329
#define MLKEM_N 256

// Barrett reduction function (matches rv64v_poly.c)
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

// Conditional add function (matches rv64v_poly.c)
static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;
  bn = __riscv_vmslt_vx_i16m1_b16(rx, 0, vl);
  rx = __riscv_vadd_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl);
  return rx;
}

// Standalone poly_reduce function (matches ML-KEM structure)
void poly_reduce(int16_t *r)
{
  size_t vl = __riscv_vsetvl_e16m1(8);  // Typical vector length for RISC-V
  vint16m1_t vt;

  for (size_t i = 0; i < MLKEM_N; i += vl)
  {
    vt = __riscv_vle16_v_i16m1(&r[i], vl);
    vt = fq_barrett(vt, vl);
    vt = fq_cadd(vt, vl);
    __riscv_vse16_v_i16m1(&r[i], vt, vl);
  }
}

// Test function that checks bounds after poly_reduce
int test_poly_reduce_bounds(int16_t *test_values, int num_values,
                            const char *test_name)
{
  printf("\nTesting %s (%d values):\n", test_name, num_values);
  printf("----------------------------------------\n");

  // Create a polynomial array and fill with test values
  int16_t poly[MLKEM_N] = {0};

  // Copy test values to beginning of polynomial
  for (int i = 0; i < num_values && i < MLKEM_N; i++)
  {
    poly[i] = test_values[i];
  }

  printf("Input values: ");
  for (int i = 0; i < num_values && i < 10; i++)
  {
    printf("%d ", poly[i]);
  }
  if (num_values > 10)
  {
    printf("...");
  }
  printf("\n");

  // Apply poly_reduce
  poly_reduce(poly);

  printf("Output values: ");
  for (int i = 0; i < num_values && i < 10; i++)
  {
    printf("%d ", poly[i]);
  }
  if (num_values > 10)
  {
    printf("...");
  }
  printf("\n");

  // Check bounds and correctness
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

  printf("Results: %d out-of-bounds, %d incorrect\n", out_of_bounds, incorrect);

  return (out_of_bounds == 0 && incorrect == 0);
}

int main()
{
  printf("Standalone poly_reduce test (matches ML-KEM structure)\n");
  printf("MLKEM_Q = %d, MLKEM_N = %d\n", MLKEM_Q, MLKEM_N);

  int total_tests = 0;
  int passed_tests = 0;

  // Test 1: Basic values
  int16_t basic_values[] = {0, 1, -1, -2, -3, 3327, 3328, 3329, 3330};
  if (test_poly_reduce_bounds(basic_values, 9, "Basic values"))
  {
    passed_tests++;
  }
  total_tests++;

  // Test 2: Values around 2*Q
  int16_t around_2q[] = {6656, 6657, 6658, 6659, 6660};
  if (test_poly_reduce_bounds(around_2q, 5, "Values around 2*Q"))
  {
    passed_tests++;
  }
  total_tests++;

  // Test 3: Large positive values
  int16_t large_pos[] = {10000, 20000, 32767};
  if (test_poly_reduce_bounds(large_pos, 3, "Large positive values"))
  {
    passed_tests++;
  }
  total_tests++;

  // Test 4: Large negative values
  int16_t large_neg[] = {-10000, -20000, -32768};
  if (test_poly_reduce_bounds(large_neg, 3, "Large negative values"))
  {
    passed_tests++;
  }
  total_tests++;

  // Test 5: Mixed values that might cause issues
  int16_t mixed[] = {-1, 3328, -2, 3327, 6657, -3329, 0, 32767, -32768};
  if (test_poly_reduce_bounds(mixed, 9, "Mixed problematic values"))
  {
    passed_tests++;
  }
  total_tests++;

  // Test 6: Full polynomial with random-like values
  int16_t full_poly[MLKEM_N];
  for (int i = 0; i < MLKEM_N; i++)
  {
    // Create pseudo-random values that might appear in ML-KEM
    full_poly[i] = (int16_t)((i * 1337 + 42) % 20000 - 10000);
  }
  if (test_poly_reduce_bounds(full_poly, MLKEM_N, "Full polynomial"))
  {
    passed_tests++;
  }
  total_tests++;

  printf("\n========================================\n");
  printf("Overall Results: %d/%d test groups passed\n", passed_tests,
         total_tests);

  if (passed_tests == total_tests)
  {
    printf("✓ All tests PASSED! poly_reduce works correctly.\n");
    return 0;
  }
  else
  {
    printf("✗ %d test groups FAILED! poly_reduce has issues.\n",
           total_tests - passed_tests);
    return 1;
  }
}
