(*<*)
theory MLKEM_Spec
  imports MLKEM_Poly_Definitions "Micro_C_Examples.C_While_Examples"
begin
(*>*)

text \<open>
  Core mathematical specification of ML-KEM polynomial arithmetic:
  coefficient-list polynomials over the integers, Barrett reduction,
  Montgomery reduction, and field multiplication (@{text fqmul}).
  All definitions operate on unbounded integers; word-level refinement
  is handled in @{text MLKEM_Refinement}.
\<close>

section \<open>Abstract Polynomial Arithmetic\<close>

text \<open>We model mlkem-native polynomials abstractly as fixed-size coefficient
  lists over the integers. This gives a clean mathematical specification
  independent of machine word sizes.\<close>

abbreviation MLKEM_N :: nat where
  \<open>MLKEM_N \<equiv> 256\<close>

type_synonym int_poly = \<open>int list\<close>

definition poly_add_int :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_add_int ps qs \<equiv> map2 (+) ps qs\<close>

definition poly_sub_int :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_sub_int ps qs \<equiv> map2 (-) ps qs\<close>

subsection \<open>Barrett Reduction\<close>

text \<open>Barrett reduction approximates division by @{text Q} using a
  pre-computed multiplier, replacing an expensive division with a
  multiplication and shift.  The result is congruent to the input
  modulo @{text Q} but not necessarily fully reduced.\<close>

abbreviation MLKEM_Q :: int where
  \<open>MLKEM_Q \<equiv> 3329\<close>

definition barrett_reduce_int :: \<open>int \<Rightarrow> int\<close> where
  \<open>barrett_reduce_int a \<equiv> a - ((20159 * a + 2^25) div 2^26) * MLKEM_Q\<close>

text \<open>Correctness: @{const barrett_reduce_int} preserves the residue class
  modulo @{const MLKEM_Q}.\<close>

theorem barrett_reduce_mod:
  shows \<open>barrett_reduce_int a mod MLKEM_Q = a mod MLKEM_Q\<close>
unfolding barrett_reduce_int_def by algebra

subsection \<open>Montgomery Reduction\<close>

text \<open>Abstract Montgomery reduction on integers. Given an integer \<open>a\<close>,
  returns a value \<open>r\<close> such that \<open>r * 2^16 \<equiv> a (mod Q)\<close>.\<close>

definition montgomery_reduce_int :: \<open>int \<Rightarrow> int\<close> where
  \<open>montgomery_reduce_int a \<equiv>
    (let t = signed_take_bit 15 ((a mod 2^16) * 62209 mod 2^16)
      in (a - t * 3329) div 2^16)\<close>

text \<open>Key refinement properties of @{const montgomery_reduce_int}.
  All proofs hide the complex \<open>signed_take_bit 15 (...)\<close> subterm
  behind a local \<open>define\<close> to keep automated provers fast.\<close>

lemma montgomery_reduce_int_result_eq:
  shows \<open>montgomery_reduce_int a * (65536::int) =
           a - signed_take_bit 15 (a mod 65536 * 62209 mod 65536) * 3329\<close>
proof -
  define u :: int where
    \<open>u = a mod 65536 * 62209 mod 65536\<close>
  define t where
    \<open>t = signed_take_bit 15 u\<close>
  have mt_def: \<open>montgomery_reduce_int a = (a - t * 3329) div 65536\<close>
    unfolding montgomery_reduce_int_def Let_def t_def u_def by simp
  \<comment> \<open>signed\_take\_bit preserves residue mod \<open>2^16\<close>\<close>
  have t_cong_u: \<open>t mod 65536 = u mod 65536\<close>
  proof -
    have \<open>t = u mod 65536 - 65536 * of_bool (bit u 15)\<close>
      unfolding t_def by (simp add: signed_take_bit_eq_take_bit_minus take_bit_eq_mod)
    thus ?thesis by simp
  qed
  \<comment> \<open>Modular congruence chain: \<open>t * Q \<equiv> a (mod 2^16)\<close>\<close>
  have s1: \<open>t * 3329 mod 65536 = u * 3329 mod 65536\<close>
    using t_cong_u by (metis mod_mult_left_eq)
  have s2: \<open>u * 3329 mod 65536 = (a mod 65536 * 62209) * 3329 mod 65536\<close>
    unfolding u_def using mod_mult_left_eq[of \<open>a mod 65536 * 62209\<close> 65536 3329] by linarith
  have s3: \<open>(a mod 65536 * 62209) * 3329 mod 65536 = a * (62209 * 3329) mod 65536\<close>
    using mod_mult_left_eq[of a 65536 \<open>62209 * 3329\<close>] by (simp only: mult.assoc)
  have qinv_q_mod: \<open>(62209::int) * 3329 mod 65536 = 1\<close>
    by simp
  have s4: \<open>a * ((62209::int) * 3329) mod 65536 = a mod 65536\<close>
    using mod_mult_right_eq[of a \<open>(62209::int) * 3329\<close> 65536] qinv_q_mod by simp
  have tQ_cong: \<open>t * 3329 mod 65536 = a mod 65536\<close>
    using s1 s2 s3 s4 by presburger
  \<comment> \<open>Exact divisibility: \<open>2^16\<close> divides \<open>a - t * Q\<close>\<close>
  have \<open>(a - t * 3329) mod 65536 = (a - a) mod 65536\<close>
    by (rule mod_diff_cong[OF refl tQ_cong])
  hence div_exact: \<open>65536 dvd (a - t * 3329)\<close>
    by (simp add: dvd_eq_mod_eq_0)
  \<comment> \<open>Combine: \<open>r * 2^16 = a - t * Q\<close>\<close>
  have \<open>montgomery_reduce_int a * 65536 = a - t * 3329\<close>
    using mt_def dvd_div_mult_self[OF div_exact] by simp
  thus ?thesis
    unfolding t_def u_def .
qed

theorem montgomery_reduce_int_correct:
  shows \<open>montgomery_reduce_int a * 2^16 mod MLKEM_Q = a mod MLKEM_Q\<close>
proof -
  define t :: int where
    \<open>t = signed_take_bit 15 (a mod 65536 * 62209 mod 65536)\<close>
  have result_eq: \<open>montgomery_reduce_int a * 65536 = a - t * 3329\<close>
    unfolding t_def by (rule montgomery_reduce_int_result_eq)
  have \<open>montgomery_reduce_int a * 2 ^ 16 mod MLKEM_Q = (a - t * MLKEM_Q) mod MLKEM_Q\<close>
    using result_eq by simp
  also have \<open>\<dots> = a mod MLKEM_Q\<close>
    by (metis mod_diff_right_eq mod_mult_self2_is_0 diff_zero)
  finally show ?thesis .
qed

text \<open>Output bound for @{const montgomery_reduce_int}: with the overflow
  precondition \<open>|a| < 2^31 - 2^15 * Q\<close>, the result fits in a signed 16-bit
  integer: \<open>|r| < 2^15\<close>.\<close>
theorem montgomery_reduce_int_bound:
  assumes \<open>\<bar>a\<bar> < 2^31 - 2^15 * MLKEM_Q\<close>
    shows \<open>\<bar>montgomery_reduce_int a\<bar> < 2^15\<close>
proof -
  define t :: int where \<open>t = signed_take_bit 15 (a mod 65536 * 62209 mod 65536)\<close>
  have result_eq: \<open>montgomery_reduce_int a * 65536 = a - t * 3329\<close>
    unfolding t_def by (rule montgomery_reduce_int_result_eq)
  have t_lb: \<open>t \<ge> -32768\<close>
  proof -
    have \<open>t \<ge> -(2^15)\<close>
      unfolding t_def by (rule signed_take_bit_int_greater_eq_minus_exp)
    thus ?thesis
      by simp
  qed
  have t_ub: \<open>t < 32768\<close>
  proof -
    have \<open>t < 2^15\<close>
      unfolding t_def by (rule signed_take_bit_int_less_exp)
    thus ?thesis
      by simp
  qed
  have a_bounds: \<open>a > -2038398976\<close> \<open>a < 2038398976\<close>
    using assms by auto
  have \<open>montgomery_reduce_int a * 65536 > -2147483648\<close>
    using result_eq a_bounds t_ub by linarith
  moreover have \<open>montgomery_reduce_int a * 65536 < 2147483648\<close>
    using result_eq a_bounds t_lb by linarith
  ultimately show ?thesis
    by simp
qed

subsection \<open>Field Multiplication\<close>

text \<open>Field multiplication in Montgomery domain: multiply two integers
  and apply @{const montgomery_reduce_int} to the product.  The result
  satisfies @{text "fqmul a b * R \<equiv> a * b (mod Q)"} where @{text "R = 2^16"}.\<close>

definition fqmul_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>fqmul_int a b \<equiv> montgomery_reduce_int (a * b)\<close>

subsection \<open>Polynomial Operations\<close>

text \<open>Coefficient-wise polynomial operations used by ML-KEM:
  Montgomery pre-scaling (by the constant @{text "1353 = R^2 mod Q"})
  and Barrett reduction modulo @{const MLKEM_Q}.\<close>

definition poly_tomont_int :: \<open>int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_tomont_int ap \<equiv> List.map (\<lambda>a. montgomery_reduce_int (a * 1353)) ap\<close>

definition poly_reduce_int :: \<open>int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_reduce_int ap \<equiv> List.map (\<lambda>a. a mod MLKEM_Q) ap\<close>

subsection \<open>Barrett Reduce Bounds\<close>

text \<open>When the input fits in a signed 16-bit word, @{const barrett_reduce_int}
  produces a result in @{text "[-1664, 1664]"}, and hence within @{text "(-Q, Q)"}.
  These bounds also hold for any integer input in that range.\<close>

lemma barrett_reduce_int_bounds:
  fixes a :: \<open>16 sword\<close>
  shows \<open>-1664 \<le> barrett_reduce_int (sint a)\<close>
    and \<open>barrett_reduce_int (sint a) \<le> 1664\<close>
(*<*)
proof -
  define q where
    \<open>q = (20159 * sint a + 33554432) div 67108864\<close>
  have sint_range: \<open>-32768 \<le> sint a\<close> \<open>sint a \<le> 32767\<close>
    using sint_range_size[of a] by (auto simp: word_size)
  have result: \<open>barrett_reduce_int (sint a) = sint a - q * 3329\<close>
    unfolding barrett_reduce_int_def q_def by simp
  have mod_eq: \<open>q * 67108864 + (20159 * sint a + 33554432) mod 67108864 = 20159 * sint a + 33554432\<close>
    unfolding q_def by (rule div_mult_mod_eq)
  have mod_lb: \<open>0 \<le> (20159 * sint a + 33554432) mod (67108864 :: int)\<close>
    by simp
  have mod_ub: \<open>(20159 * sint a + 33554432) mod (67108864 :: int) < 67108864\<close>
    by simp
  have div_lb: \<open>q * 67108864 \<le> 20159 * sint a + 33554432\<close>
    using mod_eq mod_lb by linarith
  have div_ub: \<open>20159 * sint a + 33554432 < q * 67108864 + 67108864\<close>
    using mod_eq mod_ub by linarith
  have q_lb: \<open>q \<ge> -10\<close>
    using div_ub sint_range by linarith
  have q_ub: \<open>q \<le> 10\<close>
    using div_lb sint_range by linarith
  have lower: \<open>20159 * (sint a - q * 3329) \<ge> -33558902\<close>
    using div_lb q_ub by (simp add: algebra_simps)
  have upper: \<open>20159 * (sint a - q * 3329) < 33558902\<close>
    using div_ub q_lb by (simp add: algebra_simps)
  show \<open>-1664 \<le> barrett_reduce_int (sint a)\<close>
    using result lower by simp
  show \<open>barrett_reduce_int (sint a) \<le> 1664\<close>
    using result upper by simp
qed
(*>*)

(*<*)
lemma barrett_reduce_int_in_range:
  fixes a :: \<open>16 sword\<close>
  shows \<open>- MLKEM_Q < barrett_reduce_int (sint a)\<close>
    and \<open>barrett_reduce_int (sint a) < MLKEM_Q\<close>
using barrett_reduce_int_bounds[of a] by linarith+
(*>*)

lemma barrett_reduce_int_abs_bound:
  fixes a :: \<open>16 sword\<close>
  shows \<open>\<bar>barrett_reduce_int (sint a)\<bar> < MLKEM_Q\<close>
(*<*)
using barrett_reduce_int_in_range[of a] by linarith
(*>*)

(*<*)
lemma barrett_reduce_int_bounds_int:
  assumes \<open>-32768 \<le> x\<close>
      and \<open>x \<le> 32767\<close>
    shows \<open>-1664 \<le> barrett_reduce_int x\<close>
      and \<open>barrett_reduce_int x \<le> 1664\<close>
proof -
  define q where
    \<open>q = (20159 * x + 33554432) div 67108864\<close>
  have result: \<open>barrett_reduce_int x = x - q * 3329\<close>
    unfolding barrett_reduce_int_def q_def by simp
  have mod_eq: \<open>q * 67108864 + (20159 * x + 33554432) mod 67108864 = 20159 * x + 33554432\<close>
    unfolding q_def by (rule div_mult_mod_eq)
  have mod_lb: \<open>0 \<le> (20159 * x + 33554432) mod (67108864 :: int)\<close>
    by simp
  have mod_ub: \<open>(20159 * x + 33554432) mod (67108864 :: int) < 67108864\<close>
    by simp
  have div_lb: \<open>q * 67108864 \<le> 20159 * x + 33554432\<close>
    using mod_eq mod_lb by linarith
  have div_ub: \<open>20159 * x + 33554432 < q * 67108864 + 67108864\<close>
    using mod_eq mod_ub by linarith
  have q_lb: \<open>q \<ge> -10\<close>
    using div_ub assms by linarith
  have q_ub: \<open>q \<le> 10\<close>
    using div_lb assms by linarith
  have lower: \<open>20159 * (x - q * 3329) \<ge> -33558902\<close>
    using div_lb q_ub by (simp add: algebra_simps)
  have upper: \<open>20159 * (x - q * 3329) < 33558902\<close>
    using div_ub q_lb by (simp add: algebra_simps)
  show \<open>-1664 \<le> barrett_reduce_int x\<close>
    using result lower by simp
  show \<open>barrett_reduce_int x \<le> 1664\<close>
    using result upper by simp
qed
(*>*)

lemma barrett_reduce_int_abs_bound_int:
  assumes \<open>-32768 \<le> x\<close>
      and \<open>x \<le> 32767\<close>
    shows \<open>\<bar>barrett_reduce_int x\<bar> < MLKEM_Q\<close>
(*<*)
using barrett_reduce_int_bounds_int[OF assms] by linarith
(*>*)

(*<*)
end
(*>*)
