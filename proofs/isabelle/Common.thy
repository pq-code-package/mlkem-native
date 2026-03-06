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
  \<open>poly_add_int ps qs \<equiv> map2 (+) ps qs\<close>

definition poly_sub_int :: \<open>int_poly \<Rightarrow> int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_sub_int ps qs \<equiv> map2 (-) ps qs\<close>

subsection \<open>Barrett reduction\<close>

abbreviation MLKEM_Q :: int where
  \<open>MLKEM_Q \<equiv> 3329\<close>

definition barrett_reduce_int :: \<open>int \<Rightarrow> int\<close> where
  \<open>barrett_reduce_int a \<equiv> a - ((20159 * a + 2^25) div 2^26) * MLKEM_Q\<close>

lemma barrett_reduce_mod:
  shows \<open>barrett_reduce_int a mod MLKEM_Q = a mod MLKEM_Q\<close>
unfolding barrett_reduce_int_def by algebra

subsection \<open>Montgomery reduction\<close>

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
  define u :: int where \<open>u = a mod 65536 * 62209 mod 65536\<close>
  define t where \<open>t = signed_take_bit 15 u\<close>
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

lemma montgomery_reduce_int_correct:
  shows \<open>montgomery_reduce_int a * 2^16 mod MLKEM_Q = a mod MLKEM_Q\<close>
proof -
  define t :: int where \<open>t = signed_take_bit 15 (a mod 65536 * 62209 mod 65536)\<close>
  have result_eq: \<open>montgomery_reduce_int a * 65536 = a - t * 3329\<close>
    unfolding t_def by (rule montgomery_reduce_int_result_eq)
  have \<open>montgomery_reduce_int a * 2 ^ 16 mod MLKEM_Q = (a - t * MLKEM_Q) mod MLKEM_Q\<close>
    using result_eq by simp
  also have \<open>\<dots> = a mod MLKEM_Q\<close>
    by (metis mod_diff_right_eq mod_mult_self2_is_0 diff_zero)
  finally show ?thesis .
qed

text \<open>Output bound for Montgomery reduction. With the overflow
  precondition \<open>|a| < 2^31 - 2^15 * Q\<close>, the result fits in a signed 16-bit
  integer: \<open>|r| < 2^15\<close>.\<close>
lemma montgomery_reduce_int_bound:
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
  \<open>poly_add_c p q \<equiv> update_c_mlk_poly_coeffs
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
      and \<open>no_overflow_add ar ab\<close>
      and \<open>i < MLKEM_N\<close>
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
      and \<open>no_overflow_sub ar ab\<close>
      and \<open>i < MLKEM_N\<close>
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

text \<open>Abstract pointwise map for single-polynomial in-place operations.\<close>

definition poly_tomont_int :: \<open>int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_tomont_int ap \<equiv> List.map (\<lambda>a. montgomery_reduce_int (a * 1353)) ap\<close>

definition poly_reduce_int :: \<open>int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_reduce_int ap \<equiv> List.map (\<lambda>a. a mod MLKEM_Q) ap\<close>

text \<open>Roundtrip: \<open>sint (word_of_int x)\<close> equals \<open>x\<close> when \<open>x\<close> fits in 16-bit signed range.\<close>

lemma sint_word_of_int_16:
  assumes \<open>- (2^15) \<le> x\<close>
      and \<open>x < 2^15\<close>
    shows \<open>sint (word_of_int x :: 16 sword) = x\<close>
proof -
  have \<open>signed_take_bit 15 x = x\<close>
    using assms by (intro signed_take_bit_int_eq_self) auto
  moreover have \<open>sint (word_of_int x :: 16 sword) = signed_take_bit 15 x\<close>
    by transfer simp
  ultimately show ?thesis
    by simp
qed

text \<open>The sint of \<open>word_of_int (montgomery_reduce_int (sint a * sint b))\<close> equals
  the Montgomery reduction, for any 16-bit signed inputs.\<close>

lemma sint_word_of_montgomery_fqmul:
  fixes a :: \<open>16 sword\<close>
    and b :: \<open>16 sword\<close>
  shows \<open>sint (word_of_int (montgomery_reduce_int (sint a * sint b)) :: 16 sword) =
            montgomery_reduce_int (sint a * sint b)\<close>
proof -
  have ab: \<open>\<bar>sint a\<bar> \<le> 2^15\<close> \<open>\<bar>sint b\<bar> \<le> 2^15\<close>
    using sint_range_size[where w=a] sint_range_size[where w=b] by (auto simp: word_size)
  have \<open>\<bar>sint a * sint b\<bar> \<le> 2^30\<close>
  proof -
    have \<open>\<bar>sint a * sint b\<bar> = \<bar>sint a\<bar> * \<bar>sint b\<bar>\<close>
      by (rule abs_mult)
    also have \<open>\<dots> \<le> 2^15 * 2^15\<close>
      using ab by (intro mult_mono) auto
    finally show ?thesis
      by simp
  qed
  hence \<open>\<bar>sint a * sint b\<bar> < 2^31 - 2^15 * MLKEM_Q\<close>
    by simp
  hence \<open>\<bar>montgomery_reduce_int (sint a * sint b)\<bar> < 2^15\<close>
    by (rule montgomery_reduce_int_bound)
  thus ?thesis
    by (intro sint_word_of_int_16) auto
qed

text \<open>Single-polynomial invariant step lemma: analogous to @{thm inv_list_step}
  but for unary map (single input list).\<close>

lemma inv_list_step_map:
  assumes \<open>n < length xs\<close>
    shows \<open>(take n (List.map f xs) @ drop n xs)[n := f (xs ! n)] =
              take (Suc n) (List.map f xs) @ drop (Suc n) xs\<close>
proof -
  let ?zs = \<open>List.map f xs\<close>
  from assms have ln: \<open>n < length ?zs\<close>
    by simp
  from assms have zn: \<open>?zs ! n = f (xs ! n)\<close>
    by simp
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

section \<open>Field multiplication (abstract)\<close>

definition fqmul_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>fqmul_int a b \<equiv> montgomery_reduce_int (a * b)\<close>

section \<open>Zetas table\<close>

text \<open>128 precomputed twiddle factors (signed), matching the C global
  @{verbatim "mlk_zetas[128]"} from @{file "../../mlkem/src/poly.c"}.\<close>

definition zetas_int :: \<open>int list\<close> where
  \<open>zetas_int \<equiv> [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577,
    182, 962, -1202, -1474, 1468, 573, -1325, 264, 383, -829, 1458,
    -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571, 1223,
    652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666,
    -1618, -1162, 126, 1469, -853, -90, -271, 830, 107, -1421, -247,
    -951, -398, 961, -1508, -725, 448, -1065, 677, -1275, -1103, 430,
    555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291,
    -460, 1574, 1653, -246, 778, 1159, -147, -777, 1483, -602, 1119,
    -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097, 603,
    610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220,
    -1187, -1659, -1185, -1530, -1278, 794, -1510, -854, -870, 478, -108,
    -308, 996, 991, 958, -1460, 1522, 1628]\<close>

section \<open>Mulcache computation\<close>

text \<open>Abstract mulcache: for each block of 4 coefficients, compute two
  fqmul products with the corresponding zeta factor.\<close>

definition mulcache_compute_int :: \<open>int_poly \<Rightarrow> int list\<close> where
  \<open>mulcache_compute_int ap \<equiv>
     concat (List.map (\<lambda>i. [fqmul_int (ap ! (4*i + 1)) (zetas_int ! (64 + i)),
                             fqmul_int (ap ! (4*i + 3)) (- (zetas_int ! (64 + i)))])
                      [0..<64])\<close>

lemma length_concat_map_pair:
  shows \<open>length (concat (List.map (\<lambda>j. [f j, g j]) [0..<n])) = 2 * n\<close>
by (induct n) simp_all

lemma length_mulcache_compute_int [simp]:
  shows \<open>length (mulcache_compute_int ap) = 128\<close>
unfolding mulcache_compute_int_def by (simp add: length_concat_map_pair)

lemma concat_map_pair_nth_aux:
  assumes \<open>i < n\<close>
    shows \<open>concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i) = f i
            \<and> concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i + 1) = g i\<close>
using assms proof (induct n arbitrary: i)
  case (Suc n)
  then show ?case
    by (cases \<open>i < n\<close>) (auto simp: nth_append less_Suc_eq length_concat_map_pair)
qed auto

lemma concat_map_pair_nth:
  assumes \<open>i < n\<close>
    shows \<open>concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i) = f i\<close>
      and \<open>concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i + 1) = g i\<close>
using concat_map_pair_nth_aux[OF assms] by auto

lemma mulcache_compute_int_nth_even:
  assumes \<open>i < 64\<close>
    shows \<open>mulcache_compute_int ap ! (2*i) =
             fqmul_int (ap ! (4*i + 1)) (zetas_int ! (64 + i))\<close>
unfolding mulcache_compute_int_def using assms by (rule concat_map_pair_nth)

lemma mulcache_compute_int_nth_odd:
  assumes \<open>i < 64\<close>
    shows \<open>mulcache_compute_int ap ! (2*i + 1) =
             fqmul_int (ap ! (4*i + 3)) (- (zetas_int ! (64 + i)))\<close>
unfolding mulcache_compute_int_def using assms by (rule concat_map_pair_nth)

text \<open>Concrete zetas array as 16-bit signed words. This matches the inline
  hex literal list generated by AutoCorrode from the C constant
  @{verbatim "mlk_zetas[128]"}.\<close>
definition zetas_sword :: \<open>16 sword list\<close> where
  \<open>zetas_sword \<equiv> [0xFBEC, 0xFD0A, 0xFE99, 0xFA13, 0x5D5, 0x58E, 0x11F, 0xCA,
    0xFF55, 0x26E, 0x629, 0xB6, 0x3C2, 0xFB4E, 0xFA3E, 0x5BC,
    0x23D, 0xFAD3, 0x108, 0x17F, 0xFCC3, 0x5B2, 0xF9BE, 0xFF7E,
    0xFD57, 0x3F9, 0x2DC, 0x260, 0xF9FA, 0x19B, 0xFF33, 0xF9DD,
    0x4C7, 0x28C, 0xFDD8, 0x3F7, 0xFAF3, 0x5D3, 0xFEE6, 0xF9F8,
    0x204, 0xFFF8, 0xFEC0, 0xFD66, 0xF9AE, 0xFB76, 0x7E, 0x5BD,
    0xFCAB, 0xFFA6, 0xFEF1, 0x33E, 0x6B, 0xFA73, 0xFF09, 0xFC49,
    0xFE72, 0x3C1, 0xFA1C, 0xFD2B, 0x1C0, 0xFBD7, 0x2A5, 0xFB05,
    0xFBB1, 0x1AE, 0x22B, 0x34B, 0xFB1D, 0x367, 0x60E, 0x69,
    0x1A6, 0x24B, 0xB1, 0xFF15, 0xFEDD, 0xFE34, 0x626, 0x675,
    0xFF0A, 0x30A, 0x487, 0xFF6D, 0xFCF7, 0x5CB, 0xFDA6, 0x45F,
    0xF9CA, 0x284, 0xFC98, 0x15D, 0x1A2, 0x149, 0xFF64, 0xFFB5,
    0x331, 0x449, 0x25B, 0x262, 0x52A, 0xFAFB, 0xFA47, 0x180,
    0xFB41, 0xFF78, 0x4C2, 0xFAC9, 0xFC96, 0xDC, 0xFB5D, 0xF985,
    0xFB5F, 0xFA06, 0xFB02, 0x31A, 0xFA1A, 0xFCAA, 0xFC9A, 0x1DE,
    0xFF94, 0xFECC, 0x3E4, 0x3DF, 0x3BE, 0xFA4C, 0x5F2, 0x65C]\<close>

lemma length_zetas_sword [simp]:
  shows \<open>length zetas_sword = 128\<close>
by (simp add: zetas_sword_def)

lemma map_sint_zetas_sword:
  shows \<open>List.map sint zetas_sword = zetas_int\<close>
by (simp add: zetas_sword_def zetas_int_def)

lemma zetas_sword_sint:
  assumes \<open>i < 128\<close>
    shows \<open>sint (zetas_sword ! i) = zetas_int ! i\<close>
using assms nth_map[of i zetas_sword sint] map_sint_zetas_sword by auto

lemma length_zetas_int [simp]:
  shows \<open>length zetas_int = 128\<close>
by (simp flip: map_sint_zetas_sword)

lemma map_sint_neg_scast_zetas_sword:
  shows \<open>List.map (\<lambda>w :: 16 sword. sint (scast (- (scast w :: 32 sword)) :: 16 sword))
     zetas_sword = List.map uminus zetas_int\<close>
by (simp add: zetas_sword_def zetas_int_def)

lemma zetas_neg_scast_sint:
  assumes \<open>i < 128\<close>
    shows \<open>sint (scast (- (scast (zetas_sword ! i) :: 32 sword)) :: 16 sword) =
             - (zetas_int ! i)\<close>
using assms nth_map[of i zetas_sword \<open>\<lambda>w. sint (scast (- (scast w :: 32 sword)) :: 16 sword)\<close>]
  nth_map[of i zetas_int uminus] map_sint_neg_scast_zetas_sword by simp


text \<open>Folding the partial zetas array (indices 64–127) back to @{const zetas_sword}.
  AutoCorrode eagerly evaluates @{term \<open>drop 64\<close>} on the inline constant array,
  producing a 64-element hex literal in proof goals. This lemma lets simp fold it.\<close>

lemma drop_64_zetas_sword:
  \<open>drop 64 zetas_sword =
    [0xFBB1, 0x1AE, 0x22B, 0x34B, 0xFB1D, 0x367, 0x60E, 0x69,
     0x1A6, 0x24B, 0xB1, 0xFF15, 0xFEDD, 0xFE34, 0x626, 0x675,
     0xFF0A, 0x30A, 0x487, 0xFF6D, 0xFCF7, 0x5CB, 0xFDA6, 0x45F,
     0xF9CA, 0x284, 0xFC98, 0x15D, 0x1A2, 0x149, 0xFF64, 0xFFB5,
     0x331, 0x449, 0x25B, 0x262, 0x52A, 0xFAFB, 0xFA47, 0x180,
     0xFB41, 0xFF78, 0x4C2, 0xFAC9, 0xFC96, 0xDC, 0xFB5D, 0xF985,
     0xFB5F, 0xFA06, 0xFB02, 0x31A, 0xFA1A, 0xFCAA, 0xFC9A, 0x1DE,
     0xFF94, 0xFECC, 0x3E4, 0x3DF, 0x3BE, 0xFA4C, 0x5F2, 0x65C]\<close>
  by eval

text \<open>Bounds on the abstract zetas coefficients.\<close>

lemma zetas_int_abs_bound:
  assumes \<open>i < 128\<close>
  shows \<open>\<bar>zetas_int ! i\<bar> \<le> 1659\<close>
proof -
  have \<open>list_all (\<lambda>z. \<bar>z\<bar> \<le> 1659) zetas_int\<close> by eval
  thus ?thesis using assms by (simp add: list_all_length)
qed

lemma zetas_int_bound:
  assumes \<open>i < 128\<close>
  shows \<open>zetas_int ! i \<le> 1659\<close> \<open>- (zetas_int ! i) \<le> 1659\<close>
  using zetas_int_abs_bound[OF assms] by auto

lemma zetas_int_i32_bound_from_k:
  assumes \<open>k < 64\<close>
  shows \<open>zetas_int ! (127 - k) \<le> 2147483648\<close>
    and \<open>- (zetas_int ! (127 - k)) < 2147483648\<close>
proof -
  have \<open>127 - k < 128\<close> by simp
  from zetas_int_bound[OF this]
  show \<open>zetas_int ! (127 - k) \<le> 2147483648\<close> by simp
  from zetas_int_bound[OF \<open>127 - k < 128\<close>]
  show \<open>- (zetas_int ! (127 - k)) < 2147483648\<close> by simp
qed

text \<open>Word arithmetic normalization for mulcache loop (k < 64, words are 32-bit).\<close>

lemma word_of_nat_mult_numeral:
  \<open>(numeral n :: 'a::len word) * word_of_nat k = word_of_nat (numeral n * k)\<close>
  by (metis of_nat_mult of_nat_numeral)

lemma unat_word_sub_word_of_nat:
  fixes c :: \<open>32 word\<close>
  assumes \<open>unat c = n\<close> \<open>m \<le> n\<close>
  shows \<open>unat (c - word_of_nat m) = n - m\<close>
proof -
  have \<open>n < 2 ^ 32\<close> using assms(1) unat_lt2p[of c] by simp
  hence \<open>m < 2 ^ 32\<close> using assms(2) by linarith
  hence u: \<open>unat (word_of_nat m :: 32 word) = m\<close>
    by (simp add: unat_of_nat)
  have le: \<open>(word_of_nat m :: 32 word) \<le> c\<close>
    using assms by (simp add: word_le_nat_alt u)
  show ?thesis using unat_sub[OF le] u assms by simp
qed

lemma unat_0xFD_sub_4k [simp]:
  assumes \<open>k < 64\<close>
  shows \<open>unat ((0xFD :: 32 word) - 4 * word_of_nat k) = 253 - 4 * k\<close>
  using assms
  by (simp del: of_nat_mult of_nat_numeral
           add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0xFF_sub_4k [simp]:
  assumes \<open>k < 64\<close>
  shows \<open>unat ((0xFF :: 32 word) - 4 * word_of_nat k) = 255 - 4 * k\<close>
  using assms
  by (simp del: of_nat_mult of_nat_numeral
           add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0x7E_sub_2k [simp]:
  assumes \<open>k < 64\<close>
  shows \<open>unat ((0x7E :: 32 word) - 2 * word_of_nat k) = 126 - 2 * k\<close>
  using assms
  by (simp del: of_nat_mult of_nat_numeral
           add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0x7F_sub_2k [simp]:
  assumes \<open>k < 64\<close>
  shows \<open>unat ((0x7F :: 32 word) - 2 * word_of_nat k) = 127 - 2 * k\<close>
  using assms
  by (simp del: of_nat_mult of_nat_numeral
           add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0x7F_sub_k [simp]:
  assumes \<open>k < 128\<close>
  shows \<open>unat ((0x7F :: 32 word) - word_of_nat k) = 127 - k\<close>
  using assms by (intro unat_word_sub_word_of_nat) simp_all

text \<open>Mulcache indexing with downward-counting loop variable (k counts from 63 to 0).\<close>

lemma mulcache_compute_int_nth_even':
  assumes \<open>k < 64\<close>
  shows \<open>mulcache_compute_int ap ! (126 - 2 * k) =
         fqmul_int (ap ! (253 - 4 * k)) (zetas_int ! (127 - k))\<close>
proof -
  define i where \<open>i = 63 - k\<close>
  with assms have \<open>i < 64\<close> by simp
  have idx: \<open>126 - 2 * k = 2 * i\<close> \<open>253 - 4 * k = 4 * i + 1\<close> \<open>127 - k = 64 + i\<close>
    unfolding i_def using assms by auto
  show ?thesis unfolding idx
    by (rule mulcache_compute_int_nth_even[OF \<open>i < 64\<close>])
qed

lemma mulcache_compute_int_nth_odd':
  assumes \<open>k < 64\<close>
  shows \<open>mulcache_compute_int ap ! (127 - 2 * k) =
         fqmul_int (ap ! (255 - 4 * k)) (- (zetas_int ! (127 - k)))\<close>
proof -
  define i where \<open>i = 63 - k\<close>
  with assms have \<open>i < 64\<close> by simp
  have idx: \<open>127 - 2 * k = 2 * i + 1\<close> \<open>255 - 4 * k = 4 * i + 3\<close> \<open>127 - k = 64 + i\<close>
    unfolding i_def using assms by auto
  show ?thesis unfolding idx
    by (rule mulcache_compute_int_nth_odd[OF \<open>i < 64\<close>])
qed

section \<open>NTT specification\<close>

text \<open>Structural abstract NTT following the C implementation.
  All operations on unbounded integers; overflow analysis is separate.\<close>

definition ntt_butterfly_int :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>ntt_butterfly_int zeta j blen cs \<equiv>
     let t = fqmul_int (cs ! (j + blen)) zeta in
     (cs[j + blen := cs ! j - t])[j := cs ! j + t]\<close>

fun ntt_inner_loop_int :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>ntt_inner_loop_int zeta off blen 0 cs = cs\<close>
| \<open>ntt_inner_loop_int zeta off blen (Suc cnt) cs =
     ntt_inner_loop_int zeta (Suc off) blen cnt
       (ntt_butterfly_int zeta off blen cs)\<close>

fun ntt_middle_loop_int :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat \<times> int list\<close> where
  \<open>ntt_middle_loop_int k blen 0 num_blocks cs = (k, cs)\<close>
| \<open>ntt_middle_loop_int k blen (Suc remaining) num_blocks cs =
     (let block = num_blocks - Suc remaining;
          off   = block * (2 * blen);
          zeta  = zetas_int ! k;
          cs'   = ntt_inner_loop_int zeta off blen blen cs
       in ntt_middle_loop_int (Suc k) blen remaining num_blocks cs')\<close>

fun ntt_outer_loop_int :: \<open>nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>ntt_outer_loop_int k 0 cs = cs\<close>
| \<open>ntt_outer_loop_int k (Suc layer_rem) cs =
     (let blen       = 2 ^ (Suc layer_rem);
          num_blocks = 2 ^ (6 - layer_rem);
          (k', cs')  = ntt_middle_loop_int k blen num_blocks num_blocks cs
       in ntt_outer_loop_int k' layer_rem cs')\<close>

definition poly_ntt_int :: \<open>int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_ntt_int cs \<equiv> ntt_outer_loop_int 1 7 cs\<close>

text \<open>Convenience: single NTT layer by layer number.\<close>

definition ntt_layer_int :: \<open>nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>ntt_layer_int layer cs \<equiv>
    snd (ntt_middle_loop_int (2^(layer - 1)) (2^(8 - layer))
           (2^(layer - 1)) (2^(layer - 1)) cs)\<close>

text \<open>Helper lemmas for inner loop.\<close>

lemma ntt_butterfly_int_length:
  shows \<open>length (ntt_butterfly_int z j blen cs) = length cs\<close>
  unfolding ntt_butterfly_int_def Let_def by simp

lemma ntt_inner_loop_int_length:
  shows \<open>length (ntt_inner_loop_int z off blen cnt cs) = length cs\<close>
  by (induct cnt arbitrary: off cs) (simp_all add: ntt_butterfly_int_length)

text \<open>Snoc decomposition: processing @{term \<open>Suc m\<close>} butterflies equals
  processing @{term m} then applying one more butterfly at position
  @{term \<open>off + m\<close>}.\<close>

lemma ntt_inner_loop_int_snoc:
  shows \<open>ntt_inner_loop_int z off blen (Suc m) cs =
         ntt_butterfly_int z (off + m) blen (ntt_inner_loop_int z off blen m cs)\<close>
proof (induct m arbitrary: off cs)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have \<open>ntt_inner_loop_int z off blen (Suc (Suc m)) cs =
        ntt_inner_loop_int z (Suc off) blen (Suc m) (ntt_butterfly_int z off blen cs)\<close>
    by simp
  also have \<open>\<dots> = ntt_butterfly_int z (Suc off + m) blen
        (ntt_inner_loop_int z (Suc off) blen m (ntt_butterfly_int z off blen cs))\<close>
    by (rule Suc)
  also have \<open>Suc off + m = off + Suc m\<close> by simp
  also have \<open>ntt_inner_loop_int z (Suc off) blen m (ntt_butterfly_int z off blen cs)
           = ntt_inner_loop_int z off blen (Suc m) cs\<close>
    by simp
  finally show ?case .
qed

text \<open>Coefficient bound predicate: all coefficients have absolute value less than B.\<close>

definition coeff_bound :: \<open>int \<Rightarrow> int list \<Rightarrow> bool\<close> where
  \<open>coeff_bound B cs \<equiv> \<forall>i < length cs. \<bar>cs ! i\<bar> < B\<close>

text \<open>No-overflow predicate for the inner loop.
  Ensures each butterfly step produces values in 16-bit range.\<close>

definition ntt_inner_no_overflow :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> bool\<close> where
  \<open>ntt_inner_no_overflow zeta off blen cnt acs \<equiv>
    (\<forall>m < cnt.
      let cs' = ntt_inner_loop_int zeta off blen m acs;
          j = off + m; t = fqmul_int (cs' ! (j + blen)) zeta
       in - 32768 \<le> cs' ! j + t \<and> cs' ! j + t \<le> 32767 \<and>
          - 32768 \<le> cs' ! j - t \<and> cs' ! j - t \<le> 32767)\<close>

text \<open>No-overflow predicate for a full NTT layer.\<close>

definition ntt_layer_no_overflow :: \<open>nat \<Rightarrow> int list \<Rightarrow> bool\<close> where
  \<open>ntt_layer_no_overflow l acs \<equiv> True\<close> \<comment> \<open>placeholder; sorry'd in uses\<close>

text \<open>Bound propagation through NTT layers (sorry'd for now).\<close>

lemma ntt_layer_int_bound:
  assumes \<open>coeff_bound (int l * MLKEM_Q) cs\<close> \<open>1 \<le> l\<close> \<open>l \<le> 7\<close> \<open>length cs = MLKEM_N\<close>
  shows \<open>coeff_bound (int (l + 1) * MLKEM_Q) (ntt_layer_int l cs)\<close>
  sorry

lemma poly_ntt_int_bound:
  assumes \<open>coeff_bound MLKEM_Q cs\<close> \<open>length cs = MLKEM_N\<close>
  shows \<open>coeff_bound (8 * MLKEM_Q) (poly_ntt_int cs)\<close>
  sorry

text \<open>NTT middle loop: k-index tracking.\<close>

lemma ntt_middle_loop_int_fst:
  shows \<open>fst (ntt_middle_loop_int k blen rem nb cs) = k + rem\<close>
  by (induct rem arbitrary: k cs) (auto simp: case_prod_beta Let_def)

lemma ntt_middle_loop_int_length:
  shows \<open>length (snd (ntt_middle_loop_int k blen rem nb cs)) = length cs\<close>
  by (induct rem arbitrary: k cs) (auto simp: case_prod_beta Let_def ntt_inner_loop_int_length)

text \<open>Outer loop layer composition.\<close>

lemma ntt_outer_loop_int_layer:
  assumes \<open>layer_rem \<le> 7\<close>
  shows \<open>ntt_outer_loop_int k (Suc layer_rem) cs =
    (let blen = 2 ^ (Suc layer_rem);
         nb   = 2 ^ (6 - layer_rem);
         (k', cs') = ntt_middle_loop_int k blen nb nb cs
      in ntt_outer_loop_int k' layer_rem cs')\<close>
  by simp

text \<open>Connecting zetas array to abstract spec.\<close>

lemma c_global_mlk_zetas_eq_zetas_sword:
  shows \<open>c_global_mlk_zetas = zetas_sword\<close>
  by (simp add: c_global_mlk_zetas_def zetas_sword_def)

section \<open>Inverse NTT specification\<close>

text \<open>The inverse NTT butterfly applies Barrett reduction to the sum
  and Montgomery multiplication to the difference.\<close>

definition invntt_butterfly_int :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>invntt_butterfly_int zeta j blen cs \<equiv>
     let t   = cs ! j;
         cs' = cs[j := barrett_reduce_int (t + cs ! (j + blen))]
      in cs'[j + blen := fqmul_int (cs ! (j + blen) - t) zeta]\<close>

fun invntt_inner_loop_int :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>invntt_inner_loop_int zeta off blen 0 cs = cs\<close>
| \<open>invntt_inner_loop_int zeta off blen (Suc cnt) cs =
     invntt_inner_loop_int zeta (Suc off) blen cnt
       (invntt_butterfly_int zeta off blen cs)\<close>

fun invntt_middle_loop_int :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat \<times> int list\<close> where
  \<open>invntt_middle_loop_int k blen 0 num_blocks cs = (k, cs)\<close>
| \<open>invntt_middle_loop_int k blen (Suc remaining) num_blocks cs =
     (let block = num_blocks - Suc remaining;
          off   = block * (2 * blen);
          zeta  = zetas_int ! k;
          cs'   = invntt_inner_loop_int zeta off blen blen cs
       in invntt_middle_loop_int (k - 1) blen remaining num_blocks cs')\<close>

fun invntt_outer_loop_int :: \<open>nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>invntt_outer_loop_int 0 cs = cs\<close>
| \<open>invntt_outer_loop_int (Suc n) cs =
     (let layer      = Suc n;
          blen       = 2 ^ (8 - layer);
          k          = 2 ^ layer - 1;
          num_blocks = 2 ^ (layer - 1);
          (_, cs')   = invntt_middle_loop_int k blen num_blocks num_blocks cs
       in invntt_outer_loop_int n cs')\<close>

text \<open>Full inverse NTT with Montgomery pre-scaling by 1441.\<close>

definition poly_invntt_tomont_int :: \<open>int_poly \<Rightarrow> int_poly\<close> where
  \<open>poly_invntt_tomont_int cs \<equiv>
     invntt_outer_loop_int 7 (List.map (\<lambda>c. fqmul_int c 1441) cs)\<close>

text \<open>Convenience: single inverse NTT layer by layer number.\<close>

definition invntt_layer_int :: \<open>nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>invntt_layer_int layer cs \<equiv>
    snd (invntt_middle_loop_int (2^layer - 1) (2^(8 - layer))
           (2^(layer - 1)) (2^(layer - 1)) cs)\<close>

section \<open>Additional refinement predicates\<close>

definition refines_mlk_poly_mulcache :: \<open>c_mlk_poly_mulcache \<Rightarrow> int list \<Rightarrow> bool\<close> where
  \<open>refines_mlk_poly_mulcache cm am \<longleftrightarrow>
     length (c_mlk_poly_mulcache_coeffs cm) = 128 \<and>
     List.map sint (c_mlk_poly_mulcache_coeffs cm) = am\<close>

definition refines_coeffs :: \<open>c_short list \<Rightarrow> int list \<Rightarrow> bool\<close> where
  \<open>refines_coeffs ccs acs \<longleftrightarrow> length ccs = MLKEM_N \<and> List.map sint ccs = acs\<close>

lemma refines_mlk_poly_coeffs:
  shows \<open>refines_mlk_poly cp ap \<longleftrightarrow> refines_coeffs (c_mlk_poly_coeffs cp) ap\<close>
unfolding refines_mlk_poly_def refines_coeffs_def ..

end
