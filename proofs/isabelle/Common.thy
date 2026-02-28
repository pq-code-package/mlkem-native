theory Common
  imports MLKEM_Poly_Definitions "Micro_C_Examples.C_While_Examples"
begin

section \<open>Abstract polynomial arithmetic\<close>

text \<open>We model mlkem-native polynomials abstractly as fixed-size coefficient
  lists over the integers. This gives a clean mathematical specification
  independent of machine word sizes.\<close>

abbreviation MLKEM_N :: nat where
  \<open>MLKEM_N \<equiv> 256\<close>

type_synonym int_poly = \<open>int list\<close>

definition poly_add_int :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_add_int ps qs = map2 (+) ps qs\<close>

definition poly_sub_int :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_sub_int ps qs = map2 (-) ps qs\<close>

subsection \<open>Barrett reduction\<close>

abbreviation MLKEM_Q :: int where
  \<open>MLKEM_Q \<equiv> 3329\<close>

definition barrett_reduce_int :: \<open>int \<Rightarrow> int\<close> where
  \<open>barrett_reduce_int a = a - ((20159 * a + 2^25) div 2^26) * MLKEM_Q\<close>

lemma barrett_reduce_mod:
  shows \<open>barrett_reduce_int a mod MLKEM_Q = a mod MLKEM_Q\<close>
unfolding barrett_reduce_int_def by algebra

section \<open>Concrete types and refinement\<close>

text \<open>
  Refinement relation: a concrete @{typ c_mlk_poly} refines an abstract
  @{typ int_poly} when its coefficient list has the correct length and its
  signed interpretation matches the abstract polynomial.
\<close>
definition refines_mlk_poly :: \<open>c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> bool\<close> where
  \<open>refines_mlk_poly cp ap \<longleftrightarrow>
    length (c_mlk_poly_coeffs cp) = MLKEM_N \<and>
    List.map sint (c_mlk_poly_coeffs cp) = ap\<close>

text \<open>
  No-overflow condition: the mathematical sum of each coefficient pair
  fits in a signed 16-bit integer. This is required both for the C code
  to not abort (since @{const c_signed_add} checks for overflow) and for
  the refinement to integer arithmetic to hold.
\<close>
definition no_overflow_add :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> bool\<close> where
  \<open>no_overflow_add ps qs \<longleftrightarrow>
    (\<forall>i < min (length ps) (length qs).
      ps ! i + qs ! i \<in> {-(2^15) ..< 2^15})\<close>

definition no_overflow_sub :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> bool\<close> where
  \<open>no_overflow_sub ps qs \<longleftrightarrow>
    (\<forall>i < min (length ps) (length qs).
      ps ! i - qs ! i \<in> {-(2^15) ..< 2^15})\<close>

text \<open>
  The concrete (word-level) result of polynomial addition — internal helper
  for proofs.
\<close>
definition poly_add_c :: \<open>c_mlk_poly \<Rightarrow> c_mlk_poly \<Rightarrow> c_mlk_poly\<close> where
  \<open>poly_add_c p q = update_c_mlk_poly_coeffs
    (\<lambda>_. map2 (+) (c_mlk_poly_coeffs p) (c_mlk_poly_coeffs q)) p\<close>

subsection \<open>Refinement lemmas\<close>

lemma sint_plus_no_overflow:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>sint a + sint b \<in> {-(2^(LENGTH('l) - 1)) ..< 2^(LENGTH('l) - 1)}\<close>
    shows \<open>sint (a + b) = sint a + sint b\<close>
using assms by (intro signed_arith_sint) (auto simp: word_size)

lemma sint_minus_no_overflow:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>sint a - sint b \<in> {-(2^(LENGTH('l) - 1)) ..< 2^(LENGTH('l) - 1)}\<close>
    shows \<open>sint (a - b) = sint a - sint b\<close>
using assms by (intro signed_arith_sint) (auto simp: word_size)

text \<open>
  The key refinement theorem: under the no-overflow condition, the concrete
  word-level addition produces a result that refines the abstract integer sum.
\<close>
lemma poly_add_c_refines:
  assumes \<open>refines_mlk_poly p ap\<close>
      and \<open>refines_mlk_poly q aq\<close>
      and \<open>no_overflow_add ap aq\<close>
    shows \<open>refines_mlk_poly (poly_add_c p q) (poly_add_int ap aq)\<close>
using assms by (auto simp add: c_mlk_poly.record_simps map2_map_map word_size refines_mlk_poly_def
  poly_add_c_def poly_add_int_def no_overflow_add_def intro!: nth_equalityI sint_plus_no_overflow)

subsection \<open>Auxiliary Lemmas\<close>

lemma nth_map2:
  assumes \<open>i < length xs\<close>
      and \<open>i < length ys\<close>
    shows \<open>map2 f xs ys ! i = f (xs ! i) (ys ! i)\<close>
using assms by (induction xs arbitrary: i ys) (auto simp: less_Suc_eq_0_disj split: list.splits)

lemma inv_list_step:
  assumes \<open>n < length xs\<close>
      and \<open>n < length ys\<close>
      and \<open>length xs = length ys\<close>
    shows \<open>(take n (map2 f xs ys) @ drop n xs)[n := f (xs ! n) (ys ! n)] =
              take (Suc n) (map2 f xs ys) @ drop (Suc n) xs\<close>
proof -
  let ?zs = \<open>map2 f xs ys\<close>
  from assms have ln: \<open>n < length ?zs\<close>
    by simp
  from assms have zn: \<open>?zs ! n = f (xs ! n) (ys ! n)\<close>
    by (simp add: nth_map2)
  from assms have drop_eq: \<open>drop n xs = xs ! n # drop (Suc n) xs\<close>
    by (metis Cons_nth_drop_Suc)
  have \<open>(take n ?zs @ drop n xs)[n := ?zs ! n] = take n ?zs @ (drop n xs)[0 := ?zs ! n]\<close>
    using ln by (simp add: list_update_append)
  also have \<open>\<dots> = take n ?zs @ ?zs ! n # drop (Suc n) xs\<close>
    using drop_eq by simp
  also have \<open>\<dots> = take (Suc n) ?zs @ drop (Suc n) xs\<close>
    using ln by (simp add: take_Suc_conv_app_nth)
  finally show ?thesis
    using zn by simp
qed

lemma no_overflow_add_bounds:
  assumes \<open>refines_mlk_poly vr ar\<close>
      and \<open>refines_mlk_poly vb ab\<close>
      and \<open>no_overflow_add ar ab\<close> \<open>i < MLKEM_N\<close>
    shows \<open>sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
      and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i)\<close>
proof -
  from assms(1) have lr: \<open>length (c_mlk_poly_coeffs vr) = MLKEM_N\<close>
          and mr: \<open>List.map sint (c_mlk_poly_coeffs vr) = ar\<close>
    unfolding refines_mlk_poly_def by auto
  from assms(2) have lb: \<open>length (c_mlk_poly_coeffs vb) = MLKEM_N\<close>
          and mb: \<open>List.map sint (c_mlk_poly_coeffs vb) = ab\<close>
    unfolding refines_mlk_poly_def by auto
  have \<open>ar ! i + ab ! i \<in> {-(2^15) ..< 2^15}\<close>
    using assms(3,4) lr lb mr mb unfolding no_overflow_add_def by auto
  moreover have \<open>ar ! i = sint (c_mlk_poly_coeffs vr ! i)\<close>
    using mr lr assms(4) by (simp add: nth_map[symmetric])
  moreover have \<open>ab ! i = sint (c_mlk_poly_coeffs vb ! i)\<close>
    using mb lb assms(4) by (simp add: nth_map[symmetric])
  ultimately show \<open>sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
          and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) + sint (c_mlk_poly_coeffs vb ! i)\<close>
    by auto
qed

lemma no_overflow_sub_bounds:
  assumes \<open>refines_mlk_poly vr ar\<close>
      and \<open>refines_mlk_poly vb ab\<close>
      and \<open>no_overflow_sub ar ab\<close> \<open>i < MLKEM_N\<close>
    shows \<open>sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
      and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i)\<close>
proof -
  from assms(1) have lr: \<open>length (c_mlk_poly_coeffs vr) = MLKEM_N\<close>
          and mr: \<open>List.map sint (c_mlk_poly_coeffs vr) = ar\<close>
    unfolding refines_mlk_poly_def by auto
  from assms(2) have lb: \<open>length (c_mlk_poly_coeffs vb) = MLKEM_N\<close>
          and mb: \<open>List.map sint (c_mlk_poly_coeffs vb) = ab\<close>
    unfolding refines_mlk_poly_def by auto
  have \<open>ar ! i - ab ! i \<in> {-(2^15) ..< 2^15}\<close>
    using assms(3,4) lr lb mr mb unfolding no_overflow_sub_def by auto
  moreover have \<open>ar ! i = sint (c_mlk_poly_coeffs vr ! i)\<close>
    using mr lr assms(4) by (simp add: nth_map[symmetric])
  moreover have \<open>ab ! i = sint (c_mlk_poly_coeffs vb ! i)\<close>
    using mb lb assms(4) by (simp add: nth_map[symmetric])
  ultimately show \<open>sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i) < 2 ^ 15\<close>
          and \<open>- (2 ^ 15) \<le> sint (c_mlk_poly_coeffs vr ! i) - sint (c_mlk_poly_coeffs vb ! i)\<close>
    by auto
qed

lemma MLKEM_N_sub_step [simp]:
  assumes \<open>k < MLKEM_N\<close>
    shows \<open>MLKEM_N - k = Suc (255 - k)\<close>
using assms by simp

lemma mlkem_rev_index_bound [simp]:
  shows \<open>255 - k < MLKEM_N\<close>
by simp

end
