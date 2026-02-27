theory MLKEM_Poly_Functional_Correctness
  imports Common MLKEM_Poly_Definitions iq.Isar_Explore
begin

section \<open>C verification (source-driven translation)\<close>

context c_mlk_machine_model
begin

declare c_mlk_cast_uint16_to_int16_def [micro_rust_simps del]
declare c_mlk_cast_int16_to_uint16_def [micro_rust_simps del]
declare c_mlk_ct_cmask_neg_i16_def [micro_rust_simps del]
declare c_mlk_ct_cmask_nonzero_u16_def [micro_rust_simps del]
declare nondet_choice_def [micro_rust_simps del]
declare bind2_unseq_def [micro_rust_simps del]
declare c_mlk_ct_sel_int16_def [micro_rust_simps del]
declare c_mlk_montgomery_reduce_def [micro_rust_simps del]
declare c_mlk_barrett_reduce_def [micro_rust_simps del]
declare c_mlk_scalar_signed_to_unsigned_q_def [micro_rust_simps del]
declare c_mlk_fqmul_def [micro_rust_simps del]
declare c_mlk_poly_mulcache_compute_c_def [micro_rust_simps del]
declare c_mlk_ntt_butterfly_block_def [micro_rust_simps del]
declare c_mlk_ntt_layer_def [micro_rust_simps del]
declare c_mlk_poly_ntt_c_def [micro_rust_simps del]
declare c_mlk_value_barrier_i32_def [micro_rust_simps del]
declare c_mlk_cast_int32_to_uint16_def [micro_rust_simps del]
declare c_global_mlk_zetas_def [micro_rust_simps del]

subsection \<open>\<^verbatim>\<open>mlk\_barrett\_reduce\<close> contract\<close>

definition c_mlk_barrett_reduce_contract :: \<open>c_short \<Rightarrow> ('s::{sepalg}, c_short, 'b) function_contract\<close> where
  \<open>c_mlk_barrett_reduce_contract a \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>sint r mod MLKEM_Q = sint a mod MLKEM_Q\<rangle> \<star>
               \<langle>-1664 \<le> sint r \<and> sint r \<le> 1664\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_barrett_reduce_contract

lemma barrett_sint_bounds:
    fixes a :: \<open>16 sword\<close>
  defines \<open>sa \<equiv> sint a\<close>
    shows \<open>sa \<ge> -32768\<close> \<open>sa < 32768\<close>
      and \<open>20159 * sa \<ge> -(2^31)\<close>
      and \<open>20159 * sa < 2^31\<close>
      and \<open>20159 * sa + 2^25 \<ge> -(2^31)\<close>
      and \<open>20159 * sa + 2^25 < 2^31\<close>
proof -
  have \<open>sa \<ge> -32768\<close> and \<open>sa < 32768\<close>
    using sint_range_size[where w=a] by (auto simp: sa_def word_size)
  then show \<open>sa \<ge> -32768\<close> and \<open>sa < 32768\<close> and
        \<open>20159 * sa \<ge> -(2^31)\<close> and \<open>20159 * sa < 2^31\<close> and
        \<open>20159 * sa + 2^25 \<ge> -(2^31)\<close> and \<open>20159 * sa + 2^25 < 2^31\<close>
    by auto
qed

lemma barrett_stb31_prod:
  shows \<open>signed_take_bit 31 (20159 * sint (a :: 16 sword)) = 20159 * sint a\<close>
using barrett_sint_bounds[of a] by (intro signed_take_bit_int_eq_self) auto

lemma barrett_stb31_sum:
  shows \<open>signed_take_bit 31 (20159 * sint (a :: 16 sword) + 33554432) =
          20159 * sint a + 33554432\<close>
using barrett_sint_bounds[of a] by (intro signed_take_bit_int_eq_self) auto

lemma barrett_quotient_bounds:
    fixes a :: \<open>16 sword\<close>
  defines \<open>t \<equiv> (20159 * sint a + 33554432) div (67108864 :: int)\<close>
    shows \<open>t \<ge> -10\<close>
      and \<open>t \<le> 10\<close>
proof -
  have sa: \<open>sint a \<ge> -32768\<close> \<open>sint a < 32768\<close>
    using barrett_sint_bounds[of a] by auto
  have m1: \<open>(20159::int) * (-32768) \<le> 20159 * sint a\<close>
    using sa by (intro mult_left_mono) auto
  have m2: \<open>(20159::int) * sint a \<le> 20159 * 32767\<close>
    using sa by (intro mult_left_mono) auto
  have lower: \<open>(-627015680::int) \<le> 20159 * sint a + 33554432\<close>
    using m1 by simp
  have upper: \<open>20159 * sint a + 33554432 \<le> (694104385::int)\<close>
    using m2 by simp
  have \<open>(-627015680::int) div 67108864 \<le> (20159 * sint a + 33554432) div 67108864\<close>
    using lower by (rule zdiv_mono1) auto
  thus \<open>t \<ge> -10\<close>
    unfolding t_def by simp
  have \<open>(20159 * sint a + 33554432) div 67108864 \<le> (694104385::int) div 67108864\<close>
    using upper by (rule zdiv_mono1) auto
  thus \<open>t \<le> 10\<close>
    unfolding t_def by simp
qed

lemma barrett_sint_woi:
  shows \<open>sint ((word_of_int ((20159 * sint (a::16 sword) + 33554432) div 67108864)) :: 32 sword) =
          (20159 * sint a + 33554432) div 67108864\<close>
proof -
  have t: \<open>(20159 * sint a + 33554432) div 67108864 \<ge> -10\<close>
      \<open>(20159 * sint a + 33554432) div 67108864 \<le> 10\<close>
    using barrett_quotient_bounds[of a] by auto
  show ?thesis
    by (rule sint_of_int_eq) (use t in auto)
qed

lemma barrett_stb31_tq:
  shows \<open>signed_take_bit 31 ((20159 * sint (a::16 sword) + 33554432) div 67108864 * 3329) =
          (20159 * sint a + 33554432) div 67108864 * 3329\<close>
proof -
  have \<open>(20159 * sint a + 33554432) div 67108864 \<ge> -10\<close> and \<open>(20159 * sint a + 33554432) div 67108864 \<le> 10\<close>
    using barrett_quotient_bounds[of a] by auto
  moreover from this have \<open>(3329::int) * (-10) \<le> 3329 * ((20159 * sint a + 33554432) div 67108864)\<close>
    by (intro mult_left_mono) auto
  moreover from calculation have \<open>(3329::int) * ((20159 * sint a + 33554432) div 67108864) \<le> 3329 * 10\<close>
    by (intro mult_left_mono) auto
  ultimately show ?thesis
    by (intro signed_take_bit_int_eq_self) (simp_all add: algebra_simps)
qed

lemma barrett_result_bounds:
    fixes a :: \<open>16 sword\<close>
  defines \<open>sa \<equiv> sint a\<close>
  defines \<open>t \<equiv> (20159 * sa + 33554432) div (67108864 :: int)\<close>
    shows \<open>-1664 \<le> sa - t * 3329\<close>
      and \<open>sa - t * 3329 \<le> 1664\<close>
proof -
  define r where
    \<open>r = (20159 * sa + 33554432) mod (67108864 :: int)\<close>
  have sa: \<open>sa \<ge> -32768\<close> \<open>sa < 32768\<close>
    using barrett_sint_bounds[of a] by (auto simp: sa_def)
  have r_ge: \<open>r \<ge> 0\<close>
    unfolding r_def by (intro pos_mod_sign) auto
  have r_lt: \<open>r < 67108864\<close>
    unfolding r_def by (intro pos_mod_bound) auto
  have t_r_eq: \<open>t * 67108864 + r = 20159 * sa + 33554432\<close>
    unfolding t_def r_def using div_mult_mod_eq[of \<open>20159 * sa + 33554432\<close> 67108864]
      by (simp add: algebra_simps)
  \<comment> \<open>Key: 67108864 * (sa - t * 3329) = 3329 * r - 447 * sa - 111702704128
     using 20159 * 3329 = 67108864 + 447\<close>
  have key: \<open>67108864 * (sa - t * 3329) = 3329 * r - 447 * sa - 111702704128\<close>
  proof -
    from t_r_eq have \<open>3329 * (t * 67108864 + r) = 3329 * (20159 * sa + 33554432)\<close>
      by auto
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  show \<open>-1664 \<le> sa - t * 3329\<close>
  proof (rule ccontr)
    assume \<open>\<not> (-1664 \<le> sa - t * 3329)\<close>
    hence \<open>sa - t * 3329 \<le> -1665\<close>
      by auto
    hence \<open>67108864 * (sa - t * 3329) \<le> 67108864 * (-1665)\<close>
      by (intro mult_left_mono) auto
    moreover have \<open>3329 * r - 447 * sa - 111702704128 \<ge> 0 - 447 * 32767 - 111702704128\<close>
      using r_ge sa by (intro diff_mono diff_mono) auto
    ultimately show False
      using key by simp
  qed
  show \<open>sa - t * 3329 \<le> 1664\<close>
  proof (rule ccontr)
    assume \<open>\<not> (sa - t * 3329 \<le> 1664)\<close>
    hence \<open>sa - t * 3329 \<ge> 1665\<close>
      by auto
    hence \<open>67108864 * (sa - t * 3329) \<ge> 67108864 * 1665\<close>
      by (intro mult_left_mono) auto
    moreover have \<open>3329 * r - 447 * sa - 111702704128 \<le> 3329 * 67108863 + 447 * 32768 - 111702704128\<close>
      using r_lt sa by linarith
    ultimately show False
      using key by simp
  qed
qed

lemma barrett_result_stb31:
    fixes a :: \<open>16 sword\<close>
  defines \<open>t \<equiv> (20159 * sint a + 33554432) div (67108864 :: int)\<close>
    shows \<open>-2147483648 \<le> sint a - t * 3329\<close>
      and \<open>sint a - t * 3329 < 2147483648\<close>
using barrett_result_bounds[of a] by (auto simp: t_def)

lemma barrett_quotientQ_stb31:
    fixes a :: \<open>16 sword\<close>
  defines \<open>t \<equiv> (20159 * sint a + 33554432) div (67108864 :: int)\<close>
    shows \<open>-2147483648 \<le> t * 3329\<close>
      and \<open>t * 3329 < 2147483648\<close>
using barrett_result_bounds[of a] barrett_sint_bounds[of a] by (auto simp: t_def)

lemma barrett_result_sint:
    fixes a :: \<open>16 sword\<close>
  defines \<open>t \<equiv> (20159 * sint a + 33554432) div (67108864 :: int)\<close>
    shows \<open>sint (SCAST(32 signed \<rightarrow> 16 signed)
              (SCAST(16 signed \<rightarrow> 32 signed) a - word_of_int t * (0xD01 :: 32 sword))) = sint a - t * 3329\<close>
proof -
  have res: \<open>-1664 \<le> sint a - t * 3329\<close> \<open>sint a - t * 3329 \<le> 1664\<close>
    using barrett_result_bounds[of a] by (auto simp: t_def)
  \<comment> \<open>sint of the multiplication\<close>
  have mult_sint: \<open>sint (word_of_int t * (0xD01 :: 32 sword)) = t * 3329\<close>
  proof -
    have \<open>sint (word_of_int t :: 32 sword) = t\<close>
      using barrett_sint_woi[of a] by (simp add: t_def)
    moreover have \<open>sint (0xD01 :: 32 sword) = (3329 :: int)\<close>
      by simp
    moreover have \<open>signed_take_bit 31 (t * 3329) = t * 3329\<close>
      using barrett_stb31_tq[of a] by (simp add: t_def)
    ultimately show ?thesis
      by (simp add: sint_word_mult word_size)
  qed
  \<comment> \<open>sint of the subtraction\<close>
  have sub_sint: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a - word_of_int t * 0xD01) = sint a - t * 3329\<close>
  proof -
    have up: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
      by (simp add: sint_up_scast is_up)
    have \<open>signed_take_bit 31 (sint a - t * 3329) = sint a - t * 3329\<close>
      using res by (intro signed_take_bit_int_eq_self) auto
    thus ?thesis
      by (simp add: sint_word_diff word_size up mult_sint)
  qed
  \<comment> \<open>sint of the downcast\<close>
  have scast_sint: \<open>sint (SCAST(32 signed \<rightarrow> 16 signed) w) = signed_take_bit 15 (sint w)\<close> for w :: \<open>32 sword\<close>
    by (simp only: of_int_sint_scast[symmetric] Word.sint_sbintrunc') simp
  have \<open>signed_take_bit 15 (sint a - t * 3329) = sint a - t * 3329\<close>
    using res by (intro signed_take_bit_int_eq_self) auto
  thus ?thesis
    by (simp add: scast_sint sub_sint)
qed

\<comment> \<open>TODO: move into AutoCorrode\<close>
lemma bounded_while_literal_false [micro_rust_simps]:
  shows \<open>bounded_while n (\<up>False) body = \<up>()\<close>
by (induction n) (simp_all add: micro_rust_simps)

\<comment> \<open>TODO: move into AutoCorrode\<close>
lemma c_signed_truthy_zero [micro_rust_simps]:
  shows \<open>c_signed_truthy 0 = \<up>False\<close>
by (simp add: c_signed_truthy_def)

lemma c_mlk_barrett_reduce_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_barrett_reduce while_fuel a \<Turnstile>\<^sub>F
            c_mlk_barrett_reduce_contract a\<close>
  apply (crush_boot f: c_mlk_barrett_reduce_def contract: c_mlk_barrett_reduce_contract_def)
  apply (crush_base simp add: sint_up_scast is_up sint_word_ariths
            barrett_stb31_prod barrett_stb31_sum
            signed_take_bit_int_eq_self barrett_sint_bounds
            barrett_sint_woi barrett_stb31_tq
            c_signed_truthy_zero bounded_while_literal_false)
  apply (all \<open>(insert barrett_result_bounds[of a] barrett_quotient_bounds[of a]
               barrett_sint_bounds[of a]; linarith)?\<close>)
  apply (simp_all add: barrett_result_sint mod_diff_right_eq[symmetric])
  apply (all \<open>insert barrett_result_bounds[of a]; linarith\<close>)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_add\<close> contract\<close>

text \<open>
  The contract is self-contained: refinement, well-formedness, and
  no-overflow are all expressed as pure assertions in the precondition.
  The postcondition asserts the result refines the abstract polynomial sum.
  No external assumptions needed on the specification theorem.
\<close>
definition c_mlk_poly_add_contract :: \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow> c_mlk_poly \<Rightarrow>
      int_poly \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
  \<open>c_mlk_poly_add_contract r gr vr ar b gb vb ab \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star>
               \<langle>refines_mlk_poly vr ar\<rangle> \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb \<star>
               \<langle>refines_mlk_poly vb ab\<rangle> \<star>
               \<langle>no_overflow_add ar ab\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
               \<langle>refines_mlk_poly vr' (poly_add_int ar ab)\<rangle>) \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_add_contract

lemma c_mlk_poly_add_spec:
  shows \<open>\<Gamma>; c_mlk_poly_add MLKEM_N r b \<Turnstile>\<^sub>F c_mlk_poly_add_contract r gr vr ar b gb vb ab\<close>
  apply (crush_boot f: c_mlk_poly_add_def contract: c_mlk_poly_add_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - k) (map2 (+) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_add ar ab\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - Suc k) (map2 (+) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - Suc k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - Suc k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_add ar ab\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  subgoal \<comment> \<open>Initialization + frame\<close>
    by (crush_base simp: refines_mlk_poly_def c_mlk_poly.record_simps
      poly_add_int_def no_overflow_add_def map2_map_map word_size
      intro!: nth_equalityI sint_plus_no_overflow)
  subgoal \<comment> \<open>Condition\<close>
    by crush_base (simp_all add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat)
  subgoal \<comment> \<open>Loop body\<close>
    by (crush_base simp add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
      c_mlk_poly.record_simps nth_append refines_mlk_poly_def inv_list_step)
  subgoal \<comment> \<open>Fuel exhaust\<close>
    by crush_base
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_sub\<close> contract\<close>

definition c_mlk_poly_sub_contract :: \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow> c_mlk_poly \<Rightarrow>
      int_poly \<Rightarrow> ('s, 'a, 'b) function_contract\<close> where
  \<open>c_mlk_poly_sub_contract r gr vr ar b gb vb ab \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star>
               \<langle>refines_mlk_poly vr ar\<rangle> \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb \<star>
               \<langle>refines_mlk_poly vb ab\<rangle> \<star>
               \<langle>no_overflow_sub ar ab\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
               \<langle>refines_mlk_poly vr' (poly_sub_int ar ab)\<rangle>) \<star>
               b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_sub_contract

lemma c_mlk_poly_sub_spec:
  shows \<open>\<Gamma>; c_mlk_poly_sub MLKEM_N r b \<Turnstile>\<^sub>F c_mlk_poly_sub_contract r gr vr ar b gb vb ab\<close>
  apply (crush_boot f: c_mlk_poly_sub_def contract: c_mlk_poly_sub_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - k) (map2 (-) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_sub ar ab\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>(update_c_mlk_poly_coeffs
              (\<lambda>_. take (MLKEM_N - Suc k) (map2 (-) (c_mlk_poly_coeffs vr) (c_mlk_poly_coeffs vb))
                   @ drop (MLKEM_N - Suc k) (c_mlk_poly_coeffs vr)) vr))
            \<star> b \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - Suc k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle> \<star> \<langle>refines_mlk_poly vb ab\<rangle>
            \<star> \<langle>no_overflow_sub ar ab\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  subgoal \<comment> \<open>Initialization + frame\<close>
    by (crush_base simp: refines_mlk_poly_def c_mlk_poly.record_simps
      poly_sub_int_def no_overflow_sub_def map2_map_map word_size
      intro!: nth_equalityI sint_minus_no_overflow)
  subgoal \<comment> \<open>Condition\<close>
    by crush_base (simp_all add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat)
  subgoal \<comment> \<open>Loop body\<close>
    by (crush_base simp add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
     c_mlk_poly.record_simps nth_append refines_mlk_poly_def inv_list_step)
  subgoal \<comment> \<open>Fuel exhaust\<close>
    by crush_base
  done

subsection \<open>\<^verbatim>\<open>mlk\_value\_barrier\_i32\<close> — identity (opt-blocker simplified to 0)\<close>

text \<open>After preprocessing with @{verbatim "mlk_ct_get_optblocker_i32() = 0"},
  the value barrier reduces to @{term \<open>b XOR 0 = b\<close>}.\<close>

definition c_mlk_value_barrier_i32_contract ::
  \<open>c_int \<Rightarrow> ('s::{sepalg}, c_int, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_value_barrier_i32_contract b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = b\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_value_barrier_i32_contract

lemma c_mlk_value_barrier_i32_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_value_barrier_i32 b \<Turnstile>\<^sub>F
            c_mlk_value_barrier_i32_contract b\<close>
  by (crush_boot f: c_mlk_value_barrier_i32_def
        contract: c_mlk_value_barrier_i32_contract_def)
     crush_base

subsection \<open>\<^verbatim>\<open>mlk\_cast\_int32\_to\_uint16\<close>\<close>

definition c_mlk_cast_int32_to_uint16_contract ::
  \<open>c_int \<Rightarrow> ('s::{sepalg}, c_ushort, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_cast_int32_to_uint16_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = ucast (x AND 0xFFFF)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_cast_int32_to_uint16_contract

lemma c_mlk_cast_int32_to_uint16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_cast_int32_to_uint16 x \<Turnstile>\<^sub>F
            c_mlk_cast_int32_to_uint16_contract x\<close>
  by (crush_boot f: c_mlk_cast_int32_to_uint16_def
        contract: c_mlk_cast_int32_to_uint16_contract_def)
     (crush_base simp add: scast_ucast_down_same)

subsection \<open>\<^verbatim>\<open>mlk\_cast\_uint16\_to\_int16\<close>\<close>

definition c_mlk_cast_uint16_to_int16_contract ::
  \<open>c_ushort \<Rightarrow> ('s::{sepalg}, c_short, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_cast_uint16_to_int16_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = scast x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_cast_uint16_to_int16_contract

lemma c_mlk_cast_uint16_to_int16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_cast_uint16_to_int16 x \<Turnstile>\<^sub>F
            c_mlk_cast_uint16_to_int16_contract x\<close>
  by (crush_boot f: c_mlk_cast_uint16_to_int16_def
        contract: c_mlk_cast_uint16_to_int16_contract_def)
     crush_base

subsection \<open>\<^verbatim>\<open>mlk\_ct\_cmask\_neg\_i16\<close> — negative mask\<close>

text \<open>Returns @{term \<open>0xFFFF :: c_ushort\<close>} when @{term \<open>sint x < 0\<close>},
  @{term \<open>0 :: c_ushort\<close>} otherwise.
  Implements: @{term \<open>(int32_t)x >> 16\<close>} after value-barrier identity.\<close>

definition c_mlk_ct_cmask_neg_i16_contract ::
  \<open>c_short \<Rightarrow> ('s::{sepalg}, c_ushort, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ct_cmask_neg_i16_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = (if sint x < 0 then 0xFFFF else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_ct_cmask_neg_i16_contract

text \<open>After @{const c_signed_shr}, the WP produces @{term \<open>word_of_int (sint x div 2 ^ n)\<close>}.
  For a 16-bit signed value shifted by 16, the quotient is @{term \<open>-1\<close>} (negative)
  or @{term \<open>0\<close>} (non-negative).\<close>

lemma sint16_div_65536:
  fixes x :: \<open>16 sword\<close>
  shows \<open>sint x div 65536 = (if sint x < 0 then -1 else 0)\<close>
proof -
  have \<open>sint x \<ge> -32768\<close> \<open>sint x < 32768\<close>
    using sint_range_size[where w=x] by (auto simp: word_size)
  thus ?thesis by auto
qed

lemma c_mlk_ct_cmask_neg_i16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_ct_cmask_neg_i16 x \<Turnstile>\<^sub>F
            c_mlk_ct_cmask_neg_i16_contract x\<close>
  apply (crush_boot f: c_mlk_ct_cmask_neg_i16_def
           contract: c_mlk_ct_cmask_neg_i16_contract_def)
  apply (crush_base simp add: sint_up_scast is_up
           scast_ucast_down_same sint16_div_65536)
  done

subsection \<open>\<^verbatim>\<open>mlk\_cast\_int16\_to\_uint16\<close>\<close>

definition c_mlk_cast_int16_to_uint16_contract ::
  \<open>c_int \<Rightarrow> ('s::{sepalg}, c_ushort, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_cast_int16_to_uint16_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = ucast x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_cast_int16_to_uint16_contract

lemma ucast_and_0xFFFF:
  shows \<open>UCAST(32 signed \<rightarrow> 16) (x AND 0xFFFF) = UCAST(32 signed \<rightarrow> 16) x\<close>
proof (rule word_eqI)
     fix n
  assume \<open>n < size (UCAST(32 signed \<rightarrow> 16) (x AND 0xFFFF))\<close>
  hence n16: \<open>n < 16\<close>
    by (simp add: word_size)
  have mask_eq: \<open>(0xFFFF :: 32 signed word) = mask 16\<close>
    by eval
  have \<open>(0xFFFF :: 32 signed word) !! n\<close>
    using n16 by (simp add: mask_eq nth_mask word_size)
  thus \<open>UCAST(32 signed \<rightarrow> 16) (x AND 0xFFFF) !! n = UCAST(32 signed \<rightarrow> 16) x !! n\<close>
    by (simp add: nth_ucast word_ops_nth_size word_size is_down)
qed

lemma c_mlk_cast_int16_to_uint16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_cast_int16_to_uint16 x \<Turnstile>\<^sub>F
            c_mlk_cast_int16_to_uint16_contract x\<close>
  by (crush_boot f: c_mlk_cast_int16_to_uint16_def
        contract: c_mlk_cast_int16_to_uint16_contract_def)
     (crush_base simp add: scast_ucast_down_same ucast_and_0xFFFF)

subsection \<open>\<^verbatim>\<open>mlk\_ct\_cmask\_nonzero\_u16\<close> — nonzero mask\<close>

text \<open>Returns @{term \<open>0xFFFF :: c_ushort\<close>} when @{term \<open>x \<noteq> 0\<close>},
  @{term \<open>0 :: c_ushort\<close>} otherwise.
  Implements: @{term \<open>(-(int32_t)x) >> 16\<close>} after value-barrier identity.\<close>
definition c_mlk_ct_cmask_nonzero_u16_contract ::
  \<open>c_ushort \<Rightarrow> ('s::{sepalg}, c_ushort, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ct_cmask_nonzero_u16_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = (if x \<noteq> 0 then 0xFFFF else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_ct_cmask_nonzero_u16_contract

lemma neg_uint16_div_65536:
  fixes x :: \<open>16 word\<close>
  shows \<open>(- uint x) div 65536 = (if x \<noteq> 0 then -1 else 0)\<close>
proof (cases \<open>x = 0\<close>)
  case True
  thus ?thesis
    by simp
next
  case False
  hence \<open>uint x \<noteq> 0\<close>
    by (simp add: uint_0_iff)
  hence lb: \<open>1 \<le> uint x\<close>
    using uint_ge_0[where x=x] by linarith
  have ub: \<open>uint x \<le> 65535\<close>
    using uint_lt2p[where x=x] by simp
  have \<open>(- uint x) div 65536 = -1\<close>
    by (rule int_div_pos_eq[where r=\<open>65536 - uint x\<close>])
       (use lb ub in linarith, use ub in linarith, use lb in linarith)
  with False show ?thesis
    by simp
qed

lemma sint_neg_ucast_16_32:
  fixes x :: \<open>16 word\<close>
  shows \<open>sint (- UCAST(16 \<rightarrow> 32 signed) x) = - uint x\<close>
proof -
  have s: \<open>sint (UCAST(16 \<rightarrow> 32 signed) x) = uint x\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  have lb: \<open>0 \<le> uint x\<close>
    by (rule uint_ge_0)
  have ub: \<open>uint x \<le> 2147483647\<close>
    using uint_lt2p[where x=x] by simp
  have \<open>- (2147483648 :: int) \<le> - uint x\<close>
    using ub by linarith
  moreover have \<open>- uint x < (2147483648 :: int)\<close>
    using lb by linarith
  ultimately show ?thesis
    unfolding sint_word_minus s by (simp add: signed_take_bit_int_eq_self_iff)
qed

lemma c_mlk_ct_cmask_nonzero_u16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_ct_cmask_nonzero_u16 x \<Turnstile>\<^sub>F
            c_mlk_ct_cmask_nonzero_u16_contract x\<close>
  apply (crush_boot f: c_mlk_ct_cmask_nonzero_u16_def
           contract: c_mlk_ct_cmask_nonzero_u16_contract_def)
  apply (crush_base simp add: sint_up_scast is_up is_down
           scast_ucast_down_same neg_uint16_div_65536
           sint_ucast_eq_uint ucast_and_0xFFFF
           sint_neg_ucast_16_32)
  subgoal using uint_lt2p[where x=x] uint_ge_0[where x=x] by linarith
  subgoal using uint_lt2p[where x=x] by simp
  done

subsection \<open>\<^verbatim>\<open>mlk\_ct\_sel\_int16\<close> — conditional select\<close>

text \<open>Cast round-trip helper lemmas for conditional select proof.\<close>
lemma ct_sel_cast_roundtrip':
  fixes x :: \<open>16 signed word\<close>
  shows \<open>UCAST(32 signed \<rightarrow> 16) (SCAST(16 signed \<rightarrow> 32 signed) x) = UCAST(16 signed \<rightarrow> 16) x\<close>
proof (rule word_eqI)
    fix n
  assume \<open>n < size (UCAST(32 signed \<rightarrow> 16) (SCAST(16 signed \<rightarrow> 32 signed) x))\<close>
  hence n16: \<open>n < 16\<close>
    by (simp add: word_size)
  show \<open>UCAST(32 signed \<rightarrow> 16) (SCAST(16 signed \<rightarrow> 32 signed) x) !! n = UCAST(16 signed \<rightarrow> 16) x !! n\<close>
  proof (cases \<open>n < 15\<close>)
    case True
    thus ?thesis by (simp add: nth_ucast nth_scast word_size is_up is_down)
  next
    case False
    with n16 have \<open>n = 15\<close> by linarith
    thus ?thesis by (simp add: nth_ucast nth_scast word_size is_up is_down)
  qed
qed

lemma ct_sel_cast_roundtrip:
  fixes x :: \<open>16 signed word\<close>
  shows \<open>SCAST(16 \<rightarrow> 16 signed)
          (SCAST(32 signed \<rightarrow> 16)
            (UCAST(16 \<rightarrow> 32 signed)
              (UCAST(32 signed \<rightarrow> 16)
                (SCAST(16 signed \<rightarrow> 32 signed) x)))) = x\<close>
by (simp add: ct_sel_cast_roundtrip' ucast_down_ucast_id is_down scast_ucast_down_same)

lemma ct_sel_xor_identity:
  fixes a b :: \<open>16 signed word\<close>
  shows \<open>SCAST(16 \<rightarrow> 16 signed)
          (SCAST(32 signed \<rightarrow> 16)
            (UCAST(16 \<rightarrow> 32 signed) (UCAST(32 signed \<rightarrow> 16) (SCAST(16 signed \<rightarrow> 32 signed) b))
             xor (0xFFFF :: 32 signed word)
             AND (UCAST(16 \<rightarrow> 32 signed) (UCAST(32 signed \<rightarrow> 16) (SCAST(16 signed \<rightarrow> 32 signed) a))
                  xor UCAST(16 \<rightarrow> 32 signed) (UCAST(32 signed \<rightarrow> 16) (SCAST(16 signed \<rightarrow> 32 signed) b))))) = a\<close>
proof -
  have mask_eq: \<open>(0xFFFF :: 32 signed word) = mask 16\<close>
    by eval
  show ?thesis
  proof (simp only: ct_sel_cast_roundtrip' mask_eq, rule word_eqI)
    fix n
    let ?lhs = \<open>SCAST(16 \<rightarrow> 16 signed)
          (SCAST(32 signed \<rightarrow> 16)
            (UCAST(16 \<rightarrow> 32 signed) (UCAST(16 signed \<rightarrow> 16) b) xor mask 16 AND
             (UCAST(16 \<rightarrow> 32 signed) (UCAST(16 signed \<rightarrow> 16) a) xor
              UCAST(16 \<rightarrow> 32 signed) (UCAST(16 signed \<rightarrow> 16) b))))\<close>
    assume \<open>n < size ?lhs\<close>
    hence n16: \<open>n < 16\<close> by (simp add: word_size)
    show \<open>?lhs !! n = a !! n\<close>
    proof (cases \<open>n < 15\<close>)
      case True
      thus ?thesis
        by (auto simp add: word_ops_nth_size word_size nth_ucast nth_scast is_up is_down nth_mask)
    next
      case False
      with n16 have \<open>n = 15\<close> by linarith
      thus ?thesis
        by (auto simp add: word_ops_nth_size word_size nth_ucast nth_scast is_up is_down nth_mask)
    qed
  qed
qed

text \<open>Returns @{term \<open>a\<close>} when @{term \<open>cond \<noteq> 0\<close>}, @{term \<open>b\<close>} otherwise.\<close>
definition c_mlk_ct_sel_int16_contract ::
  \<open>c_short \<Rightarrow> c_short \<Rightarrow> c_ushort \<Rightarrow> ('s::{sepalg}, c_short, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ct_sel_int16_contract a b cond \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = (if cond \<noteq> 0 then a else b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_ct_sel_int16_contract

lemma c_mlk_ct_sel_int16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_ct_sel_int16 a b cond \<Turnstile>\<^sub>F
            c_mlk_ct_sel_int16_contract a b cond\<close>
  apply (crush_boot f: c_mlk_ct_sel_int16_def
           contract: c_mlk_ct_sel_int16_contract_def)
  apply crush_base
  apply (simp_all add: ct_sel_cast_roundtrip ct_sel_xor_identity)
  done

subsection \<open>\<^verbatim>\<open>mlk\_montgomery\_reduce\<close> contract\<close>

text \<open>The contract states that the result refines the abstract Montgomery
  reduction: the signed interpretation of the return value equals
  @{const montgomery_reduce_int} applied to the signed interpretation
  of the input. The precondition bounds the input to prevent overflow.\<close>
definition c_mlk_montgomery_reduce_contract ::
  \<open>c_int \<Rightarrow> ('s::{sepalg}, c_short, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_montgomery_reduce_contract a \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>\<bar>sint a\<bar> < 2^31 - 2^15 * MLKEM_Q\<rangle>;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>sint r = montgomery_reduce_int (sint a)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_montgomery_reduce_contract

text \<open>Bound on t * Q: since \<open>|sint t| \<le> 32768\<close> and
  \<open>32768 * 3329 < 2^31\<close>, multiplication does not overflow.\<close>
lemma montgomery_t_mul_Q_bounds:
  fixes t :: \<open>16 signed word\<close>
  shows \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) * MLKEM_Q < 2147483648\<close>
    and \<open>-2147483648 \<le> sint (SCAST(16 signed \<rightarrow> 32 signed) t) * MLKEM_Q\<close>
proof -
  have \<open>sint t \<ge> -32768\<close> \<open>sint t < 32768\<close>
    using sint_range_size[where w=t] by (auto simp: word_size)
  hence st: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) \<ge> -32768\<close>
            \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) < 32768\<close>
    by (simp_all add: sint_up_scast is_up)
  show \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) * MLKEM_Q < 2147483648\<close>
    using st by (auto intro: order_le_less_trans[OF mult_right_mono])
  show \<open>-2147483648 \<le> sint (SCAST(16 signed \<rightarrow> 32 signed) t) * MLKEM_Q\<close>
    using st by (auto intro: le_trans[OF _ mult_right_mono])
qed

text \<open>Bound on \<open>a - t * Q\<close>: with \<open>|sint a| < 2^31 - 2^15 * Q\<close> and
  \<open>|sint t * Q| \<le> 32768 * 3329 \<approx> 10^8\<close>, the subtraction fits in 32 bits.\<close>
lemma montgomery_sub_bounds:
    fixes a :: \<open>32 signed word\<close> and t :: \<open>16 signed word\<close>
  assumes \<open>\<bar>sint a\<bar> < 2^31 - 2^15 * MLKEM_Q\<close>
    shows \<open>sint a - sint (SCAST(16 signed \<rightarrow> 32 signed) t * 0xD01) < 2147483648\<close>
      and \<open>-2147483648 \<le> sint a - sint (SCAST(16 signed \<rightarrow> 32 signed) t * 0xD01)\<close>
proof -
  have ta: \<open>sint a > -2038398976\<close> \<open>sint a < 2038398976\<close>
    using assms by auto
  have st: \<open>sint t \<ge> -32768\<close> \<open>sint t < 32768\<close>
    using sint_range_size[where w=t] by (auto simp: word_size)
  hence st32: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) \<ge> -32768\<close>
              \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) < 32768\<close>
    by (simp_all add: sint_up_scast is_up)
  have mul_lo: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) * 3329 \<ge> (-32768) * 3329\<close>
    using st32 by (intro mult_right_mono) auto
  have mul_hi: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t) * 3329 \<le> 32767 * 3329\<close>
    using st32 by (intro mult_right_mono) auto
  have stb: \<open>signed_take_bit 31 (sint (SCAST(16 signed \<rightarrow> 32 signed) t) * 3329) =
              sint (SCAST(16 signed \<rightarrow> 32 signed) t) * 3329\<close>
    using mul_lo mul_hi by (intro signed_take_bit_int_eq_self) auto
  have sint_mul: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t * 0xD01) =
                   sint (SCAST(16 signed \<rightarrow> 32 signed) t) * 3329\<close>
    by (simp add: sint_word_mult word_size stb)
  show \<open>sint a - sint (SCAST(16 signed \<rightarrow> 32 signed) t * 0xD01) < 2147483648\<close>
    using ta mul_lo by (simp add: sint_mul)
  show \<open>-2147483648 \<le> sint a - sint (SCAST(16 signed \<rightarrow> 32 signed) t * 0xD01)\<close>
    using ta mul_hi by (simp add: sint_mul)
qed

text \<open>The word-level computation of Montgomery's \<open>t\<close> equals the abstract
  integer-level computation.\<close>
lemma montgomery_t_sint:
    fixes a :: \<open>32 signed word\<close>
  defines \<open>t_w \<equiv> SCAST(16 \<rightarrow> 16 signed) (UCAST(32 \<rightarrow> 16)
                   (UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))
                    * 0xF301 AND 0xFFFF))\<close>
    shows \<open>sint t_w = signed_take_bit 15 ((sint a mod 2^16) * 62209 mod 2^16)\<close>
proof -
  \<comment> \<open>SCAST(16 \<rightarrow> 16 signed) preserves sint (same-length cast)\<close>
  let ?inner = \<open>UCAST(32 \<rightarrow> 16)
     (UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))
      * 0xF301 AND 0xFFFF)\<close>
  have step1: \<open>sint t_w = sint ?inner\<close>
    unfolding t_w_def by (simp add: sint_up_scast is_up)
  \<comment> \<open>For a 16-bit word, sint = signed_take_bit 15 . uint\<close>
  have step2: \<open>sint ?inner = signed_take_bit 15 (uint ?inner)\<close>
    by (simp add: sint_uint word_size)
  \<comment> \<open>UCAST(32\<rightarrow>16) preserves signed_take_bit 15 of uint\<close>
  let ?prod = \<open>UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))
               * 0xF301 AND (0xFFFF :: 32 word)\<close>
  have step3: \<open>signed_take_bit 15 (uint (UCAST(32 \<rightarrow> 16) ?prod)) =
               signed_take_bit 15 (uint ?prod)\<close>
  proof -
    have rw: \<open>UCAST(32 \<rightarrow> 16) ?prod = word_of_int (uint ?prod)\<close>
      by (rule ucast_eq)
    have len: \<open>LENGTH(16) = Suc 15\<close>
      by (simp add: word_size)
    show ?thesis
      by (simp only: rw uint_word_of_int_eq len sbintrunc_bintrunc)
  qed
  \<comment> \<open>uint of AND 0xFFFF = uint mod 2^16\<close>
  let ?mul = \<open>UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF)) * (0xF301 :: 32 word)\<close>
  have step4: \<open>uint (?mul AND 0xFFFF) = uint ?mul mod 65536\<close>
  proof -
    have \<open>(0xFFFF :: 32 word) = mask 16\<close>
      by eval
    show ?thesis
      by (subst \<open>(0xFFFF :: 32 word) = mask 16\<close>)
         (simp add: and_mask_mod_2p uint_word_of_int word_size)
  qed
  \<comment> \<open>uint of multiplication\<close>
  have step5: \<open>uint ?mul = uint (UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))) * 62209 mod 2^32\<close>
    by (simp add: uint_word_ariths word_size)
  \<comment> \<open>uint of up-cast UCAST(16\<rightarrow>32) = uint of inner\<close>
  have step6: \<open>uint (UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))) =
                  uint (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))\<close>
    by (simp add: uint_up_ucast is_up)
  \<comment> \<open>uint of down-cast UCAST(32 signed\<rightarrow>16) = uint mod 2^16\<close>
  have step7: \<open>uint (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF)) = uint (a AND 0xFFFF) mod 2^16\<close>
  proof -
    have rw: \<open>UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF) = word_of_int (uint (a AND 0xFFFF))\<close>
      by (rule ucast_eq)
    show ?thesis
      by (simp only: rw uint_word_of_int_eq take_bit_eq_mod) (simp add: word_size)
  qed
  \<comment> \<open>uint of AND 0xFFFF = uint a mod 2^16\<close>
  have step8: \<open>uint (a AND (0xFFFF :: 32 signed word)) = uint a mod 65536\<close>
  proof -
    have \<open>(0xFFFF :: 32 signed word) = mask 16\<close>
      by eval
    show ?thesis
      by (subst \<open>(0xFFFF :: 32 signed word) = mask 16\<close>)
         (simp add: and_mask_mod_2p uint_word_of_int word_size take_bit_eq_mod)
  qed
  \<comment> \<open>Chain: uint of the up-cast = uint a mod 65536\<close>
  have uint_chain: \<open>uint (UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))) = uint a mod 65536\<close>
    using step6 step7 step8 by simp
  \<comment> \<open>The product does not overflow 32 bits: (uint a mod 65536) * 62209 < 2^32\<close>
  have no_overflow: \<open>(uint a mod 65536) * 62209 < 2^32\<close>
  proof -
    have \<open>uint a mod 65536 < 65536\<close>
      by simp
    hence \<open>(uint a mod 65536) * 62209 < 65536 * 62209\<close>
      by (rule mult_strict_right_mono) simp
    also have \<open>\<dots> < 2^32\<close>
      by simp
    finally show ?thesis
      .
  qed
  \<comment> \<open>Combine: signed_take_bit 15 of the uint chain\<close>
  have lhs_eq: \<open>sint t_w = signed_take_bit 15 ((uint a mod 65536) * 62209 mod 65536)\<close>
  proof -
    have \<open>uint ?mul = (uint a mod 65536) * 62209\<close>
      using step5 uint_chain no_overflow by simp
    hence \<open>uint (?mul AND 0xFFFF) = (uint a mod 65536) * 62209 mod 65536\<close>
      using step4 by simp
    hence \<open>signed_take_bit 15 (uint ?prod) =
           signed_take_bit 15 ((uint a mod 65536) * 62209 mod 65536)\<close>
      by simp
    thus ?thesis using step1 step2 step3 by simp
  qed
  \<comment> \<open>Finally: uint a mod 65536 = sint a mod 65536 (since 2^16 | 2^32)\<close>
  have \<open>uint a mod 65536 = sint a mod 65536\<close>
    by (simp add: uint_sint word_size take_bit_eq_mod mod_mod_cancel)
  thus ?thesis
    using lhs_eq by simp
qed

text \<open>The full Montgomery result at the word level equals the abstract
  \<open>montgomery_reduce_int\<close> applied to \<open>sint a\<close>.\<close>
lemma montgomery_result_sint:
    fixes a :: \<open>32 signed word\<close>
  assumes \<open>\<bar>sint a\<bar> < 2^31 - 2^15 * MLKEM_Q\<close>
    shows \<open>sint (SCAST(32 signed \<rightarrow> 16 signed)
            (word_of_int (sint (a - SCAST(16 signed \<rightarrow> 32 signed)
              (SCAST(16 \<rightarrow> 16 signed) (UCAST(32 \<rightarrow> 16)
                (UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))
                 * 0xF301 AND 0xFFFF))) * 0xD01) div 65536))) =
          montgomery_reduce_int (sint a)\<close>
proof -
  define t_w where \<open>t_w \<equiv> SCAST(16 \<rightarrow> 16 signed) (UCAST(32 \<rightarrow> 16)
    (UCAST(16 \<rightarrow> 32) (UCAST(32 signed \<rightarrow> 16) (a AND 0xFFFF))
     * 0xF301 AND 0xFFFF))\<close>
  \<comment> \<open>sint of t_w equals the abstract montgomery t\<close>
  have t_sint: \<open>sint t_w = signed_take_bit 15 ((sint a mod 2^16) * 62209 mod 2^16)\<close>
    unfolding t_w_def by (rule montgomery_t_sint)
  \<comment> \<open>sint of the upcast preserves value\<close>
  have sint_cast: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t_w) = sint t_w\<close>
    by (simp add: sint_up_scast is_up)
  \<comment> \<open>Subtraction bounds from montgomery_sub_bounds\<close>
  note sub_bounds = montgomery_sub_bounds[OF assms, where t=t_w, folded t_w_def]
  \<comment> \<open>sint of the subtraction\<close>
  have sint_sub: \<open>sint (a - SCAST(16 signed \<rightarrow> 32 signed) t_w * 0xD01) =
    sint a - sint (SCAST(16 signed \<rightarrow> 32 signed) t_w * 0xD01)\<close>
    using sub_bounds
    by (simp add: sint_word_diff word_size signed_take_bit_int_eq_self)
  \<comment> \<open>sint of multiplication t_w * Q\<close>
  have sint_mul: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t_w * 0xD01) =
    sint t_w * 3329\<close>
  proof -
    note mul_bounds = montgomery_t_mul_Q_bounds[where t=t_w]
    have \<open>signed_take_bit 31 (sint (SCAST(16 signed \<rightarrow> 32 signed) t_w) * 3329) =
          sint (SCAST(16 signed \<rightarrow> 32 signed) t_w) * 3329\<close>
      using mul_bounds by (intro signed_take_bit_int_eq_self) auto
    thus ?thesis by (simp add: sint_word_mult word_size sint_cast)
  qed
  \<comment> \<open>The div expression equals montgomery_reduce_int\<close>
  have div_eq: \<open>sint (a - SCAST(16 signed \<rightarrow> 32 signed) t_w * 0xD01) div 65536 =
    montgomery_reduce_int (sint a)\<close>
    using sint_sub sint_mul t_sint
    unfolding montgomery_reduce_int_def Let_def by simp
  \<comment> \<open>Result bound ensures the final cast preserves value\<close>
  have result_bound: \<open>\<bar>montgomery_reduce_int (sint a)\<bar> < 2^15\<close>
    using assms by (rule montgomery_reduce_int_bound)
  \<comment> \<open>sint of SCAST(32s\<rightarrow>16s)(word_of_int k) = k when |k| < 2^15\<close>
  define r where \<open>r = montgomery_reduce_int (sint a)\<close>
  have \<open>sint (SCAST(32 signed \<rightarrow> 16 signed) (word_of_int r :: 32 signed word)) = r\<close>
  proof -
    have \<open>sint (word_of_int r :: 32 signed word) = r\<close>
      using result_bound unfolding r_def by (intro sint_of_int_eq) auto
    hence \<open>SCAST(32 signed \<rightarrow> 16 signed) (word_of_int r :: 32 signed word) =
           (word_of_int r :: 16 signed word)\<close>
      by (simp add: scast_def)
    moreover have \<open>sint (word_of_int r :: 16 signed word) = r\<close>
      using result_bound unfolding r_def by (intro sint_of_int_eq) (auto simp: word_size)
    ultimately show ?thesis by simp
  qed
  thus ?thesis using div_eq by (simp add: t_w_def r_def)
qed

lemma c_mlk_montgomery_reduce_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_montgomery_reduce while_fuel a \<Turnstile>\<^sub>F
            c_mlk_montgomery_reduce_contract a\<close>
  apply (crush_boot f: c_mlk_montgomery_reduce_def
           contract: c_mlk_montgomery_reduce_contract_def)
  apply crush_base
  apply (all \<open>(insert montgomery_t_mul_Q_bounds montgomery_sub_bounds[OF _]; simp; fail)?\<close>)
  apply (simp add: montgomery_result_sint)
  done

subsection \<open>\<^verbatim>\<open>mlk\_fqmul\<close> contract\<close>

text \<open>Field multiplication: @{term \<open>fqmul a b = montgomery_reduce (a * b)\<close>}.
  Since both inputs are 16-bit signed, the product fits in 32-bit signed
  and satisfies the Montgomery precondition unconditionally.\<close>
lemma fqmul_product_bound:
  fixes a b :: \<open>16 signed word\<close>
  shows \<open>\<bar>sint a * sint b\<bar> < 2 ^ 31 - 2 ^ 15 * MLKEM_Q\<close>
proof -
  have \<open>sint a \<ge> -32768\<close> \<open>sint a \<le> 32767\<close>
    using sint_range_size[where w=a] by (auto simp: word_size)
  hence a_abs: \<open>\<bar>sint a\<bar> \<le> 32768\<close>
    by auto
  have \<open>sint b \<ge> -32768\<close> \<open>sint b \<le> 32767\<close>
    using sint_range_size[where w=b] by (auto simp: word_size)
  hence b_abs: \<open>\<bar>sint b\<bar> \<le> 32768\<close>
    by auto
  have \<open>\<bar>sint a * sint b\<bar> = \<bar>sint a\<bar> * \<bar>sint b\<bar>\<close>
    by (rule abs_mult)
  also have \<open>\<dots> \<le> 32768 * 32768\<close>
    using a_abs b_abs by (intro mult_mono) auto
  also have \<open>(32768 * 32768 :: int) < 2 ^ 31 - 2 ^ 15 * MLKEM_Q\<close>
    by simp
  finally show ?thesis .
qed

lemma fqmul_sint_product:
  fixes a b :: \<open>16 signed word\<close>
  shows \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a * SCAST(16 signed \<rightarrow> 32 signed) b) =
         sint a * sint b\<close>
using fqmul_product_bound[of a b] by (simp add: sint_word_mult sint_up_scast is_up
  sbintrunc_eq_in_range range_sbintrunc word_size, linarith)

definition c_mlk_fqmul_contract ::
  \<open>c_short \<Rightarrow> c_short \<Rightarrow> ('s::{sepalg}, c_short, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_fqmul_contract a b \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>sint r = montgomery_reduce_int (sint a * sint b)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_fqmul_contract

lemma c_mlk_fqmul_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_fqmul while_fuel while_fuel a b \<Turnstile>\<^sub>F
            c_mlk_fqmul_contract a b\<close>
  apply (crush_boot f: c_mlk_fqmul_def contract: c_mlk_fqmul_contract_def)
  apply crush_base
  apply (insert fqmul_product_bound[of a b])
  apply (simp_all add: fqmul_sint_product sint_up_scast is_up)
  done

subsection \<open>\<^verbatim>\<open>mlk\_scalar\_signed\_to\_unsigned\_q\<close> contract\<close>

text \<open>Converts a signed value in \<open>(-MLKEM_Q, MLKEM_Q)\<close> to its
  canonical unsigned representative in \<open>[0, MLKEM_Q)\<close>.
  Adds \<open>MLKEM_Q\<close> if the input is negative.\<close>
lemma scalar_unsigned_q_cast_sint:
  assumes \<open>-MLKEM_Q < sint c\<close> \<open>sint c < 0\<close>
    shows \<open>sint (SCAST(32 signed \<rightarrow> 16 signed)
          (SCAST(16 signed \<rightarrow> 32 signed) c + 0xD01)) = sint c mod MLKEM_Q\<close>
proof -
  have scast_sint: \<open>sint (SCAST(32 signed \<rightarrow> 16 signed) w) = signed_take_bit 15 (sint w)\<close> for w :: \<open>32 sword\<close>
    by (simp only: of_int_sint_scast[symmetric] Word.sint_sbintrunc') simp
  have up: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) c) = sint c\<close>
    by (simp add: sint_up_scast is_up)
  have add_sint: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) c + 0xD01) = sint c + 3329\<close>
  proof -
    have \<open>signed_take_bit 31 (sint c + 3329) = sint c + 3329\<close>
      using sint_range_size[where w=c] by (intro signed_take_bit_int_eq_self) (auto simp: word_size)
    thus ?thesis
      by (simp add: sint_word_ariths word_size up)
  qed
  have stb15: \<open>signed_take_bit 15 (sint c + 3329) = sint c + 3329\<close>
    using assms by (intro signed_take_bit_int_eq_self) auto
  have cast_eq: \<open>sint (SCAST(32 signed \<rightarrow> 16 signed) (SCAST(16 signed \<rightarrow> 32 signed) c + 0xD01)) = sint c + 3329\<close>
    by (simp add: scast_sint add_sint stb15)
  have mod_eq: \<open>sint c mod 3329 = sint c + 3329\<close>
    using assms by (intro int_mod_pos_eq[where q="-1"]) auto
  show ?thesis
    by (simp add: cast_eq mod_eq)
qed

definition c_mlk_scalar_signed_to_unsigned_q_contract ::
  \<open>c_short \<Rightarrow> ('s::{sepalg}, c_short, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_scalar_signed_to_unsigned_q_contract c \<equiv>
    let pre  = can_alloc_reference \<star> \<langle>-MLKEM_Q < sint c \<and> sint c < MLKEM_Q\<rangle>;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>sint r = sint c mod MLKEM_Q\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_scalar_signed_to_unsigned_q_contract

lemma c_mlk_scalar_signed_to_unsigned_q_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_scalar_signed_to_unsigned_q while_fuel c \<Turnstile>\<^sub>F
            c_mlk_scalar_signed_to_unsigned_q_contract c\<close>
  apply (crush_boot f: c_mlk_scalar_signed_to_unsigned_q_def
           contract: c_mlk_scalar_signed_to_unsigned_q_contract_def)
  apply crush_base
  apply (simp_all add: scalar_unsigned_q_cast_sint sint_up_scast is_up)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_tomont\_c\<close> contract\<close>

definition c_mlk_poly_tomont_c_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_tomont_c_contract r gr vr ar \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star>
               \<langle>refines_mlk_poly vr ar\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
               \<langle>refines_mlk_poly vr' (poly_tomont_int ar)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_tomont_c_contract

lemma c_mlk_poly_tomont_c_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_tomont_c while_fuel while_fuel MLKEM_N r \<Turnstile>\<^sub>F
            c_mlk_poly_tomont_c_contract r gr vr ar\<close>
  apply (crush_boot f: c_mlk_poly_tomont_c_def contract: c_mlk_poly_tomont_c_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
            \<langle>length (c_mlk_poly_coeffs vr') = MLKEM_N\<rangle> \<star>
            \<langle>\<forall>j < MLKEM_N - k. sint (c_mlk_poly_coeffs vr' ! j) =
                montgomery_reduce_int (sint (c_mlk_poly_coeffs vr ! j) * 1353)\<rangle> \<star>
            \<langle>\<forall>j. MLKEM_N - k \<le> j \<longrightarrow> j < MLKEM_N \<longrightarrow>
                c_mlk_poly_coeffs vr' ! j = c_mlk_poly_coeffs vr ! j\<rangle>)
            \<star> (\<Squnion>gf. xa \<mapsto>\<langle>\<top>\<rangle> gf\<down>(0x549 :: c_short))
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
            \<langle>length (c_mlk_poly_coeffs vr') = MLKEM_N\<rangle> \<star>
            \<langle>\<forall>j < MLKEM_N - Suc k. sint (c_mlk_poly_coeffs vr' ! j) =
                montgomery_reduce_int (sint (c_mlk_poly_coeffs vr ! j) * 1353)\<rangle> \<star>
            \<langle>\<forall>j. MLKEM_N - Suc k \<le> j \<longrightarrow> j < MLKEM_N \<longrightarrow>
                c_mlk_poly_coeffs vr' ! j = c_mlk_poly_coeffs vr ! j\<rangle>)
            \<star> (\<Squnion>gf. xa \<mapsto>\<langle>\<top>\<rangle> gf\<down>(0x549 :: c_short))
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - Suc k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  apply crush_base
  apply (crush_base simp add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
      c_mlk_poly.record_simps nth_append nth_list_update refines_mlk_poly_def
      poly_tomont_int_def sint_word_of_montgomery_fqmul)
  apply (auto intro!: nth_equalityI)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_tomont\<close> contract\<close>

definition c_mlk_poly_tomont_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_tomont_contract r gr vr ar \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star>
               \<langle>refines_mlk_poly vr ar\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
               \<langle>refines_mlk_poly vr' (poly_tomont_int ar)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_tomont_contract

declare c_mlk_poly_tomont_c_def [micro_rust_simps del]

lemma c_mlk_poly_tomont_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_tomont MLKEM_N while_fuel while_fuel r \<Turnstile>\<^sub>F
            c_mlk_poly_tomont_contract r gr vr ar\<close>
  apply (crush_boot f: c_mlk_poly_tomont_def contract: c_mlk_poly_tomont_contract_def)
  apply (rule wp_callI[OF c_mlk_poly_tomont_c_spec[where gr=gr and vr=vr and ar=ar]])
  apply (simp add: c_mlk_poly_tomont_c_contract_def)
  apply (crush_base simp add: c_mlk_poly_tomont_c_contract_def)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_reduce\_c\<close> contract\<close>

definition c_mlk_poly_reduce_c_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_reduce_c_contract r gr vr ar \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star>
               \<langle>refines_mlk_poly vr ar\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
               \<langle>refines_mlk_poly vr' (poly_reduce_int ar)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_reduce_c_contract

lemma c_mlk_poly_reduce_c_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_reduce_c while_fuel while_fuel MLKEM_N r \<Turnstile>\<^sub>F
            c_mlk_poly_reduce_c_contract r gr vr ar\<close>
  apply (crush_boot f: c_mlk_poly_reduce_c_def contract: c_mlk_poly_reduce_c_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
            \<langle>length (c_mlk_poly_coeffs vr') = MLKEM_N\<rangle> \<star>
            \<langle>\<forall>j < MLKEM_N - k. sint (c_mlk_poly_coeffs vr' ! j) =
                sint (c_mlk_poly_coeffs vr ! j) mod MLKEM_Q\<rangle> \<star>
            \<langle>\<forall>j. MLKEM_N - k \<le> j \<longrightarrow> j < MLKEM_N \<longrightarrow>
                c_mlk_poly_coeffs vr' ! j = c_mlk_poly_coeffs vr ! j\<rangle>)
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
            \<langle>length (c_mlk_poly_coeffs vr') = MLKEM_N\<rangle> \<star>
            \<langle>\<forall>j < MLKEM_N - Suc k. sint (c_mlk_poly_coeffs vr' ! j) =
                sint (c_mlk_poly_coeffs vr ! j) mod MLKEM_Q\<rangle> \<star>
            \<langle>\<forall>j. MLKEM_N - Suc k \<le> j \<longrightarrow> j < MLKEM_N \<longrightarrow>
                c_mlk_poly_coeffs vr' ! j = c_mlk_poly_coeffs vr ! j\<rangle>)
            \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - Suc k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly vr ar\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  apply (crush_base simp add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
      c_mlk_poly.record_simps nth_append nth_list_update refines_mlk_poly_def
      poly_reduce_int_def
      c_mlk_barrett_reduce_contract_def c_mlk_scalar_signed_to_unsigned_q_contract_def
      c_signed_truthy_zero bounded_while_literal_false)
  apply (auto intro!: nth_equalityI)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_reduce\<close> contract\<close>

definition c_mlk_poly_reduce_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_reduce_contract r gr vr ar \<equiv>
    let pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>vr \<star>
               \<langle>refines_mlk_poly vr ar\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' vr'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>vr' \<star>
               \<langle>refines_mlk_poly vr' (poly_reduce_int ar)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_reduce_contract

declare c_mlk_poly_reduce_c_def [micro_rust_simps del]

lemma c_mlk_poly_reduce_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_reduce MLKEM_N while_fuel while_fuel r \<Turnstile>\<^sub>F
            c_mlk_poly_reduce_contract r gr vr ar\<close>
  apply (crush_boot f: c_mlk_poly_reduce_def contract: c_mlk_poly_reduce_contract_def)
  apply (rule wp_callI[OF c_mlk_poly_reduce_c_spec[where gr=gr and vr=vr and ar=ar]])
  apply (simp add: c_mlk_poly_reduce_c_contract_def)
  apply (crush_base simp add: c_mlk_poly_reduce_c_contract_def)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_mulcache\_compute\_c\<close> contract\<close>

text \<open>Computes the multiplication cache: 128 products of odd-indexed
  coefficients with corresponding zeta factors.\<close>
definition c_mlk_poly_mulcache_compute_c_contract ::
  \<open>('addr, 8 word list, c_mlk_poly_mulcache) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly_mulcache \<Rightarrow>
   ('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_mulcache_compute_c_contract x gx vx a ga va aa \<equiv>
    let pre  = can_alloc_reference \<star>
               x \<mapsto>\<langle>\<top>\<rangle> gx\<down>vx \<star>
               a \<mapsto>\<langle>\<top>\<rangle> ga\<down>va \<star>
               \<langle>refines_mlk_poly va aa\<rangle> \<star>
               \<langle>length (c_mlk_poly_mulcache_coeffs vx) = 128\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gx' vx'. x \<mapsto>\<langle>\<top>\<rangle> gx'\<down>vx' \<star>
               \<langle>refines_mlk_poly_mulcache vx' (mulcache_compute_int aa)\<rangle>) \<star>
               a \<mapsto>\<langle>\<top>\<rangle> ga\<down>va
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_mulcache_compute_c_contract

text \<open>NOTE: The fuel parameters in the function call may need adjustment
  once the generated definition @{verbatim "c_mlk_poly_mulcache_compute_c_def"}
  is inspected.\<close>
lemma c_mlk_poly_mulcache_compute_c_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_mulcache_compute_c while_fuel while_fuel 64 x a \<Turnstile>\<^sub>F
            c_mlk_poly_mulcache_compute_c_contract x gx vx a ga va aa\<close>
  apply (crush_boot f: c_mlk_poly_mulcache_compute_c_def
                   contract: c_mlk_poly_mulcache_compute_c_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gx' vx'. x \<mapsto>\<langle>\<top>\<rangle> gx'\<down>vx' \<star>
            \<langle>length (c_mlk_poly_mulcache_coeffs vx') = 128\<rangle> \<star>
            \<langle>\<forall>j < 2 * (64 - k). sint (c_mlk_poly_mulcache_coeffs vx' ! j) =
                mulcache_compute_int aa ! j\<rangle>)
            \<star> a \<mapsto>\<langle>\<top>\<rangle> ga\<down>va
            \<star> (\<Squnion>gi. xa \<mapsto>\<langle>\<top>\<rangle> gi\<down>(of_nat (64 - k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly va aa\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gx' vx'. x \<mapsto>\<langle>\<top>\<rangle> gx'\<down>vx' \<star>
            \<langle>length (c_mlk_poly_mulcache_coeffs vx') = 128\<rangle> \<star>
            \<langle>\<forall>j < 2 * (64 - Suc k). sint (c_mlk_poly_mulcache_coeffs vx' ! j) =
                mulcache_compute_int aa ! j\<rangle>)
            \<star> a \<mapsto>\<langle>\<top>\<rangle> ga\<down>va
            \<star> (\<Squnion>gi. xa \<mapsto>\<langle>\<top>\<rangle> gi\<down>(of_nat (64 - Suc k) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>refines_mlk_poly va aa\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  subgoal \<comment> \<open>Init + Finalization\<close>
    by (crush_base simp add: refines_mlk_poly_mulcache_def
        c_mlk_poly_mulcache.record_simps length_mulcache_compute_int)
       (auto intro!: nth_equalityI)
  subgoal \<comment> \<open>Condition check\<close>
    by (crush_base simp add: word_less_nat_alt unat_of_nat
        c_trunc_div_int_def
        c_signed_truthy_zero bounded_while_literal_false) auto
  subgoal \<comment> \<open>Loop body\<close>
    apply (crush_base simp add: word_less_nat_alt unat_of_nat
        c_mlk_poly_mulcache.record_simps c_mlk_poly.record_simps
        nth_list_update refines_mlk_poly_def
        c_mlk_fqmul_contract_def fqmul_int_def
        mulcache_compute_int_nth_even mulcache_compute_int_nth_odd
        c_trunc_div_int_def
        c_signed_truthy_zero bounded_while_literal_false
        length_mulcache_compute_int)
    using [[linarith_split_limit = 20]]
    apply (simp_all add: word_less_nat_alt unat_of_nat word_le_nat_alt
        sint_up_scast is_up c_global_mlk_zetas_def
        mulcache_compute_int_nth_even' mulcache_compute_int_nth_odd'
        fqmul_int_def nth_map
        drop_64_zetas_sword[symmetric] nth_drop length_zetas_sword
        zetas_sword_sint zetas_neg_scast_sint
        zetas_int_i32_bound_from_k)
    done
  subgoal \<comment> \<open>Fuel exhaust\<close>
    by (crush_base simp add: c_trunc_div_int_def)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_mulcache\_compute\<close> contract\<close>

definition c_mlk_poly_mulcache_compute_contract ::
  \<open>('addr, 8 word list, c_mlk_poly_mulcache) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly_mulcache \<Rightarrow>
   ('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_mulcache_compute_contract x gx vx a ga va aa \<equiv>
    let pre  = can_alloc_reference \<star>
               x \<mapsto>\<langle>\<top>\<rangle> gx\<down>vx \<star>
               a \<mapsto>\<langle>\<top>\<rangle> ga\<down>va \<star>
               \<langle>refines_mlk_poly va aa\<rangle> \<star>
               \<langle>length (c_mlk_poly_mulcache_coeffs vx) = 128\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gx' vx'. x \<mapsto>\<langle>\<top>\<rangle> gx'\<down>vx' \<star>
               \<langle>refines_mlk_poly_mulcache vx' (mulcache_compute_int aa)\<rangle>) \<star>
               a \<mapsto>\<langle>\<top>\<rangle> ga\<down>va
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_mulcache_compute_contract

lemma c_mlk_poly_mulcache_compute_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_mulcache_compute 64 while_fuel while_fuel x a \<Turnstile>\<^sub>F
            c_mlk_poly_mulcache_compute_contract x gx vx a ga va aa\<close>
  apply (crush_boot f: c_mlk_poly_mulcache_compute_def
                   contract: c_mlk_poly_mulcache_compute_contract_def)
  apply (rule wp_callI[OF c_mlk_poly_mulcache_compute_c_spec
           [where gx=gx and vx=vx and ga=ga and va=va and aa=aa]])
  apply (simp add: c_mlk_poly_mulcache_compute_c_contract_def)
  apply (crush_base simp add: c_mlk_poly_mulcache_compute_c_contract_def)
  done

subsection \<open>\<^verbatim>\<open>mlk\_ntt\_butterfly\_block\<close> contract\<close>

text \<open>Inner loop: applies butterflies to one block of coefficients.
  Works at the coefficient-list level via @{const refines_coeffs}.\<close>
definition c_mlk_ntt_butterfly_block_contract ::
  \<open>('addr, 8 word list, c_short list) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
   c_short list \<Rightarrow> int list \<Rightarrow>
   c_short \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow> nat \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ntt_butterfly_block_contract r gr cs acs zeta start_v len_v bound_v n \<equiv>
    let off  = unat start_v;
        blen = unat len_v;
        pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>cs \<star>
               \<langle>refines_coeffs cs acs\<rangle> \<star>
               \<langle>off + 2 * blen \<le> MLKEM_N\<rangle> \<star>
               \<langle>blen > 0\<rangle> \<star>
               \<langle>ntt_inner_no_overflow (sint zeta) off blen blen acs\<rangle> \<star>
               \<langle>blen \<le> n\<rangle> \<star>
               \<langle>MLKEM_N \<le> size r\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
               \<langle>refines_coeffs cs'
                  (ntt_inner_loop_int (sint zeta) off blen blen acs)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_ntt_butterfly_block_contract

lemma unat_add_no_overflow_from_bound:
  assumes \<open>unat (a :: 32 word) + 2 * unat (b :: 32 word) \<le> 256\<close>
    shows \<open>unat (a + b) = unat a + unat b\<close>
proof -
  from assms have \<open>unat a + unat b \<le> 256\<close>
    by linarith
  hence \<open>unat a + unat b < 4294967296\<close>
    by linarith
  thus ?thesis
    by (simp add: unat_word_ariths)
qed

lemma unat_butterfly_idx:
    fixes start_v len_v :: \<open>32 word\<close>
  assumes \<open>unat start_v + 2 * unat len_v \<le> MLKEM_N\<close>
      and \<open>n - Suc k < unat len_v\<close>
      and \<open>Suc k \<le> n\<close>
      and \<open>unat len_v \<le> n\<close>
    shows \<open>unat (start_v + (word_of_nat n - (1 + word_of_nat k)) + len_v) =
              unat start_v + (n - Suc k) + unat len_v\<close>
      and \<open>unat (start_v + (word_of_nat n - (1 + word_of_nat k))) =
              unat start_v + (n - Suc k)\<close>
      and \<open>unat start_v + (n - Suc k) + unat len_v < MLKEM_N\<close>
      and \<open>unat start_v + (n - Suc k) < MLKEM_N\<close>
proof -
  from assms have diff_bound: \<open>n - Suc k < 256\<close>
    by linarith
  have sum_bound: \<open>unat start_v + (n - Suc k) + unat len_v < 256\<close>
    using assms diff_bound by linarith
  have sum_bound2: \<open>unat start_v + (n - Suc k) < 256\<close>
    using sum_bound by linarith
  show bound1: \<open>unat start_v + (n - Suc k) + unat len_v < MLKEM_N\<close>
    using sum_bound by simp
  show bound2: \<open>unat start_v + (n - Suc k) < MLKEM_N\<close>
    using sum_bound2 by simp
  have word_sub: \<open>(word_of_nat n :: 32 word) - (1 + word_of_nat k) = word_of_nat (n - Suc k)\<close>
    using assms(3) by (simp add: word_of_nat_eq_iff of_nat_diff)
  hence sub_unat: \<open>unat ((word_of_nat n :: 32 word) - (1 + word_of_nat k)) = (n - Suc k) mod 4294967296\<close>
    by (simp add: unat_of_nat)
  have sub_eq: \<open>unat ((word_of_nat n :: 32 word) - (1 + word_of_nat k)) = n - Suc k\<close>
    using sub_unat diff_bound by simp
  show mid: \<open>unat (start_v + (word_of_nat n - (1 + word_of_nat k))) = unat start_v + (n - Suc k)\<close>
    using sub_eq sum_bound2 by (simp add: unat_word_ariths)
  show \<open>unat (start_v + (word_of_nat n - (1 + word_of_nat k)) + len_v)
       = unat start_v + (n - Suc k) + unat len_v\<close>
    using mid sum_bound by (simp add: unat_word_ariths)
qed

lemma ntt_butterfly_block_fc_step:
    fixes ra :: \<open>c_short list\<close>
      and rb :: \<open>c_short\<close>
      and cs :: \<open>c_short list\<close>
      and z :: \<open>int\<close>
      and off blen n k :: \<open>nat\<close>
  assumes ra_eq: \<open>list.map sint ra = ntt_inner_loop_int z off blen (n - Suc k) (list.map sint cs)\<close>
      and rb_eq: \<open>sint rb = montgomery_reduce_int (sint (ra ! (off + n + blen - Suc k)) * z)\<close>
      and overflow: \<open>ntt_inner_no_overflow z off blen blen (list.map sint cs)\<close>
      and m_bound: \<open>n - Suc k < blen\<close>
      and k_bound: \<open>Suc k \<le> n\<close>
      and sum_bound: \<open>off + 2 * blen \<le> MLKEM_N\<close>
      and len_ra: \<open>length ra = MLKEM_N\<close>
    shows \<open>list.map sint (ra[off + n + blen - Suc k := ra ! (off + n - Suc k) - rb,
                            off + n - Suc k := ra ! (off + n - Suc k) + rb]) =
            ntt_inner_loop_int z off blen (n - k) (list.map sint cs)\<close>
proof -
  define m where \<open>m = n - Suc k\<close>
  with k_bound have m_suc: \<open>n - k = Suc m\<close>
    by simp
  from m_def k_bound have idx_hi: \<open>off + n + blen - Suc k = off + m + blen\<close>
    by simp
  from m_def k_bound have idx_lo: \<open>off + n - Suc k = off + m\<close>
    by simp
  from m_bound m_def sum_bound len_ra have hi_bound: \<open>off + m + blen < length ra\<close> and lo_bound: \<open>off + m < length ra\<close>
    by auto
  \<comment> \<open>Abstract state after m iterations\<close>
  define L where \<open>L = ntt_inner_loop_int z off blen m (list.map sint cs)\<close>
  have L_eq: \<open>L = list.map sint ra\<close>
    using ra_eq m_def L_def by simp
  have L_lo: \<open>L ! (off + m) = sint (ra ! (off + m))\<close>
    using L_eq lo_bound by (simp add: nth_map)
  have L_hi: \<open>L ! (off + m + blen) = sint (ra ! (off + m + blen))\<close>
    using L_eq hi_bound by (simp add: nth_map)
  \<comment> \<open>Montgomery result\<close>
  define t where \<open>t = fqmul_int (L ! (off + m + blen)) z\<close>
  have t_eq: \<open>t = sint rb\<close>
    unfolding t_def fqmul_int_def L_hi using rb_eq idx_hi by simp
  \<comment> \<open>Extract overflow bounds from predicate\<close>
  have ob: \<open>- 32768 \<le> L ! (off + m) + t \<and> L ! (off + m) + t \<le> 32767 \<and>
            - 32768 \<le> L ! (off + m) - t \<and> L ! (off + m) - t \<le> 32767\<close>
    using overflow m_bound m_def unfolding ntt_inner_no_overflow_def Let_def L_def t_def by auto
  \<comment> \<open>sint distributes over + and -\<close>
  have sint_add: \<open>sint (ra ! (off + m) + rb) = sint (ra ! (off + m)) + sint rb\<close>
    by (rule sint_plus_no_overflow) (use ob L_lo t_eq in auto)
  have sint_sub: \<open>sint (ra ! (off + m) - rb) = sint (ra ! (off + m)) - sint rb\<close>
    by (rule sint_minus_no_overflow) (use ob L_lo t_eq in auto)
  \<comment> \<open>RHS: expand via snoc + butterfly\<close>
  have rhs_eq: \<open>ntt_inner_loop_int z off blen (Suc m) (list.map sint cs) =
                  (L[off + m + blen := L ! (off + m) - t])[off + m := L ! (off + m) + t]\<close>
    unfolding L_def ntt_inner_loop_int_snoc ntt_butterfly_int_def Let_def t_def by simp
  \<comment> \<open>LHS: push map sint through updates, substitute\<close>
  have lhs_eq: \<open>list.map sint (ra[off + m + blen := ra ! (off + m) - rb,
                                   off + m := ra ! (off + m) + rb]) =
                  (L[off + m + blen := L ! (off + m) - t])[off + m := L ! (off + m) + t]\<close>
    using L_eq sint_add sint_sub L_lo t_eq lo_bound hi_bound by (simp add: List.map_update)
  show ?thesis
    unfolding idx_hi idx_lo m_suc using lhs_eq rhs_eq by simp
qed

lemma c_mlk_ntt_butterfly_block_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_ntt_butterfly_block while_fuel while_fuel n
              r zeta start_v len_v bound_v \<Turnstile>\<^sub>F
            c_mlk_ntt_butterfly_block_contract r gr cs acs zeta start_v len_v bound_v n\<close>
  apply (crush_boot f: c_mlk_ntt_butterfly_block_def
                   contract: c_mlk_ntt_butterfly_block_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
            \<langle>refines_coeffs cs'
                (ntt_inner_loop_int (sint zeta) (unat start_v) (unat len_v)
                    (min (n - k) (unat len_v)) acs)\<rangle>)
            \<star> (\<Squnion>gj. x \<mapsto>\<langle>\<top>\<rangle> gj\<down>(of_nat (unat start_v + min (n - k) (unat len_v)) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>ntt_inner_no_overflow (sint zeta) (unat start_v) (unat len_v) (unat len_v) acs\<rangle>
            \<star> \<langle>unat start_v + 2 * unat len_v \<le> MLKEM_N\<rangle>
            \<star> \<langle>MLKEM_N \<le> size r\<rangle>
            \<star> \<langle>k \<le> n\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
            \<langle>refines_coeffs cs'
                (ntt_inner_loop_int (sint zeta) (unat start_v) (unat len_v)
                    (n - Suc k) acs)\<rangle>)
            \<star> (\<Squnion>gj. x \<mapsto>\<langle>\<top>\<rangle> gj\<down>(of_nat (unat start_v + (n - Suc k)) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>ntt_inner_no_overflow (sint zeta) (unat start_v) (unat len_v) (unat len_v) acs\<rangle>
            \<star> \<langle>unat start_v + 2 * unat len_v \<le> MLKEM_N\<rangle>
            \<star> \<langle>MLKEM_N \<le> size r\<rangle>
            \<star> \<langle>Suc k \<le> n\<rangle>
            \<star> \<langle>n - Suc k < unat len_v\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
  subgoal \<comment> \<open>Init + Finalization\<close>
    by (crush_base simp add: min_absorb2)
  subgoal \<comment> \<open>Condition check\<close>
    by crush_base (auto simp add: word_less_nat_alt unat_of_nat
            unat_add_no_overflow_from_bound min_le_iff_disj min_less_iff_conj)
  subgoal \<comment> \<open>Loop body\<close>
    apply (crush_base simp add: word_less_nat_alt unat_of_nat
        unat_butterfly_idx ntt_inner_no_overflow_def
        refines_coeffs_def ntt_inner_loop_int_snoc
        ntt_butterfly_int_def fqmul_int_def nth_list_update
        ntt_inner_loop_int_length)
    apply (auto simp: ntt_inner_no_overflow_def Let_def fqmul_int_def
        intro: ntt_butterfly_block_fc_step)
    done
  subgoal \<comment> \<open>Fuel exhaust\<close>
    by (crush_base simp add: min_absorb2)
  done

subsection \<open>\<^verbatim>\<open>mlk\_ntt\_layer\<close> contract\<close>

text \<open>Middle loop: applies one NTT layer (all butterfly blocks for a given len).\<close>

definition c_mlk_ntt_layer_contract ::
  \<open>('addr, 8 word list, c_short list) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
   c_short list \<Rightarrow> int list \<Rightarrow>
   c_uint \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ntt_layer_contract r gr cs acs layer_val \<equiv>
    let l    = unat layer_val;
        pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>cs \<star>
               \<langle>refines_coeffs cs acs\<rangle> \<star>
               \<langle>1 \<le> l \<and> l \<le> 7\<rangle> \<star>
               \<langle>ntt_layer_no_overflow l acs\<rangle> \<star>
               \<langle>MLKEM_N \<le> size r\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
               \<langle>refines_coeffs cs' (ntt_layer_int l acs)\<rangle>)
    in make_function_contract pre post\<close>
ucincl_auto c_mlk_ntt_layer_contract

lemma c_global_mlk_zetas_sint:
  assumes \<open>i < 128\<close>
   shows \<open>sint (c_global_mlk_zetas ! i) = zetas_int ! i\<close>
using assms by (simp add: c_global_mlk_zetas_def zetas_sword_def[symmetric] zetas_sword_sint)

lemma ntt_layer_total_size:
  assumes \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
    shows \<open>2 ^ (l - 1) * (2 * 2 ^ (8 - l)) = MLKEM_N\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  then show ?thesis
    by auto
qed

lemma ntt_layer_k_bound:
  assumes \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>j < 2 ^ (l - 1)\<close>
    shows \<open>2 ^ (l - 1) + j < (128 :: nat)\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by auto
qed

lemma ntt_layer_nb_le_N:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
    shows \<open>2 ^ (l - Suc 0) \<le> MLKEM_N\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  then show ?thesis
    by auto
qed

lemma drop_bit_0x100_eq:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
    shows \<open>drop_bit l (0x100 :: 32 word) = 2 ^ (8 - l)\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  then show ?thesis
    by auto
qed

lemma ntt_layer_total_size_word:
  assumes \<open>Suc 0 \<le> l\<close> \<open>l \<le> 7\<close>
    shows \<open>(2 :: 32 word) ^ (l - Suc 0) * (2 * 2 ^ (8 - l)) = 0x100\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  then show ?thesis
    by auto
qed

lemma word_of_nat_mult_numeral_right:
  shows \<open>word_of_nat k * (numeral n :: 'a::len word) = word_of_nat (k * numeral n)\<close>
by (metis of_nat_mult of_nat_numeral)

lemma ntt_layer_start_cond:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>((word_of_nat (min (255 - k) (2 ^ (l - Suc 0))) :: 32 word) * (2 * 2 ^ (8 - l)) < 0x100) =
              (255 - k < 2 ^ (l - Suc 0))\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  then show ?thesis using assms
    by (auto simp del: of_nat_mult
             simp add: word_of_nat_mult_numeral word_of_nat_mult_numeral_right
                  word_less_nat_alt unat_of_nat unat_sub word_le_nat_alt
                  min_def ntt_layer_total_size_word)
qed

lemma ntt_layer_cond_false_min:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>\<not> (255 - k < 2 ^ (l - Suc 0))\<close>
    shows \<open>min (255 - (k::nat)) (2 ^ (l - Suc 0)) = min MLKEM_N (2 ^ (l - Suc 0))\<close>
using assms ntt_layer_nb_le_N[of l] by (simp add: min_def)

lemma word_of_nat_255_sub:
  assumes \<open>k \<le> 255\<close>
    shows \<open>(word_of_nat (255 - k) :: 32 word) = 0xFF - word_of_nat k\<close>
using assms by (simp add: of_nat_diff)

lemma unat_minus_1_bound:
  assumes \<open>Suc 0 \<le> unat v\<close>
      and \<open>unat (v :: 32 word) \<le> 7\<close>
    shows \<open>unat (v - 1) < 32\<close>
using assms by (simp add: unat_sub word_le_nat_alt)

lemma min_from_Suc_less:
  assumes \<open>n - Suc k < m\<close>
      and \<open>Suc k \<le> n\<close>
    shows \<open>min (n - k) m = n - (k :: nat)\<close>
proof -
  from assms have \<open>n - k \<le> m\<close>
    by linarith
  thus ?thesis
    by (simp add: min_absorb1)
qed

lemma ntt_layer_blen_le_N:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
    shows \<open>2 ^ (8 - l) \<le> MLKEM_N\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  then show ?thesis
    by auto
qed

lemma ntt_layer_unat_k_index:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - k < 2 ^ (l - Suc 0)\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>unat ((2::32 word) ^ (l - Suc 0) + (0xFF - word_of_nat k)) = 2 ^ (l - Suc 0) + (255 - k)\<close>
proof -
  from assms have l_cases: \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by (auto simp: unat_of_nat of_nat_diff unat_sub word_le_nat_alt)
qed

lemma ntt_layer_unat_offset:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>unat ((0xFF - word_of_nat k) * (2 * (2::32 word) ^ (8 - l))) = (255 - k) * (2 * 2 ^ (8 - l))\<close>
proof -
  from assms have l_cases: \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  have eq: \<open>(0xFF :: 32 word) - word_of_nat k = word_of_nat (255 - k)\<close>
    using assms by (simp add: of_nat_diff)
  have w2: \<open>(2 :: 32 word) * 2 ^ (8 - l) = word_of_nat (2 * 2 ^ (8 - l))\<close>
    using l_cases by (elim insertE emptyE; simp)
  have bound: \<open>(255 - k) * (2 * 2 ^ (8 - l)) < 2 ^ 32\<close>
    using l_cases assms by (elim insertE emptyE; simp)
  show ?thesis
    unfolding eq w2 of_nat_mult[symmetric] unat_of_nat using bound by (simp add: mod_less)
qed

lemma ntt_middle_loop_int_step:
  shows \<open>ntt_inner_loop_int (zetas_int ! (k + j)) (j * (2 * blen)) blen blen
           (snd (ntt_middle_loop_int k blen j j cs)) =
         snd (ntt_middle_loop_int (Suc k) blen j (Suc j)
           (ntt_inner_loop_int (zetas_int ! k) 0 blen blen cs))\<close>
by (simp add: ntt_middle_loop_int_snoc[symmetric] ntt_middle_loop_int.simps(2) Let_def)

lemma ntt_layer_fuel_not_exhausted:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - k < 2 ^ (l - Suc 0)\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>2 ^ (l - Suc 0) + 255 - k < (128 :: nat)\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by auto
qed

lemma ntt_layer_offset_bound:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - k < 2 ^ (l - Suc 0)\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>(255 - k) * 2 * 2 ^ (8 - l) + 2 * 2 ^ (8 - l) \<le> MLKEM_N\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by auto
qed

lemma c_mlk_ntt_layer_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_ntt_layer MLKEM_N while_fuel while_fuel MLKEM_N
              r layer_val \<Turnstile>\<^sub>F
            c_mlk_ntt_layer_contract r gr cs acs layer_val\<close>
  apply (crush_boot f: c_mlk_ntt_layer_def
                   contract: c_mlk_ntt_layer_contract_def)
  apply crush_base
  subgoal for x xa xb \<comment> \<open>Main while loop\<close>
    apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>k. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
              \<langle>refines_coeffs cs'
                  (snd (ntt_middle_loop_int (2^(unat layer_val - 1)) (2^(8 - unat layer_val))
                      (min (MLKEM_N - k) (2^(unat layer_val - 1)))
                      (min (MLKEM_N - k) (2^(unat layer_val - 1))) acs))\<rangle>)
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat (min (MLKEM_N - k) (2^(unat layer_val - 1)) * (2 * 2^(8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gk. xa \<mapsto>\<langle>\<top>\<rangle> gk\<down>(of_nat (2^(unat layer_val - 1) + min (MLKEM_N - k) (2^(unat layer_val - 1))) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2^(8 - unat layer_val)) :: c_uint))
              \<star> can_alloc_reference
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle>  \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>ntt_layer_no_overflow (unat layer_val) acs\<rangle>
              \<star> \<langle>k \<le> MLKEM_N\<rangle>
              \<star> \<langle>MLKEM_N \<le> size r\<rangle>\<close>
          and INV'=\<open>\<lambda>k. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
              \<langle>refines_coeffs cs'
                  (snd (ntt_middle_loop_int (2^(unat layer_val - 1)) (2^(8 - unat layer_val))
                      (MLKEM_N - Suc k) (MLKEM_N - Suc k) acs))\<rangle>)
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat ((MLKEM_N - Suc k) * (2 * 2^(8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gk. xa \<mapsto>\<langle>\<top>\<rangle> gk\<down>(of_nat (2^(unat layer_val - 1) + (MLKEM_N - Suc k)) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2^(8 - unat layer_val)) :: c_uint))
              \<star> can_alloc_reference
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle>  \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>ntt_layer_no_overflow (unat layer_val) acs\<rangle>
              \<star> \<langle>Suc k \<le> MLKEM_N\<rangle>
              \<star> \<langle>MLKEM_N - Suc k < 2^(unat layer_val - 1)\<rangle>
              \<star> \<langle>MLKEM_N \<le> size r\<rangle>\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
    subgoal \<comment> \<open>Init + Finalization\<close>
      by (crush_base simp add: min_absorb2 ntt_layer_int_def ntt_layer_total_size ntt_layer_nb_le_N
              unat_sub word_le_nat_alt drop_bit_0x100_eq)
    subgoal \<comment> \<open>Condition check\<close>
      by crush_base (simp_all add: ntt_layer_start_cond ntt_layer_cond_false_min
              word_of_nat_255_sub)
    subgoal \<comment> \<open>Loop body\<close>
      \<comment> \<open>Phase 1: VCG without zetas literal\<close>
      apply (crush_base simp add: bind2_unseq_def refines_coeffs_def min_absorb2
          word_less_nat_alt unat_of_nat word_le_nat_alt unat_sub
          ntt_layer_k_bound ntt_layer_total_size ntt_layer_total_size_word
          ntt_layer_nb_le_N
          ntt_middle_loop_int_length ntt_inner_loop_int_length)
      \<comment> \<open>Phase 2: finish VCG, folding zetas literal to zetas_sword\<close>
      apply (crush_base simp add:
          c_global_mlk_zetas_def zetas_sword_def[symmetric]
          zetas_sword_sint
          bind2_unseq_def refines_coeffs_def min_absorb2
          word_less_nat_alt unat_of_nat word_le_nat_alt unat_sub
          ntt_layer_k_bound ntt_layer_total_size ntt_layer_total_size_word
          ntt_layer_no_overflow_block ntt_layer_nb_le_N
          ntt_middle_loop_int_snoc[symmetric]
          ntt_middle_loop_int_length ntt_inner_loop_int_length)
      \<comment> \<open>Phase 3: close remaining pure goals\<close>
      apply (simp_all only: ntt_layer_blen_le_N ntt_layer_k_bound ntt_layer_nb_le_N
          ntt_layer_total_size ntt_layer_unat_k_index ntt_layer_unat_offset
          ntt_middle_loop_int_step[symmetric])
      apply (simp_all only: One_nat_def[symmetric] mult.assoc[symmetric]
          ntt_layer_no_overflow_block)
      \<comment> \<open>6 goals: offset, start_arith, fuel (\<times>2)\<close>
      apply (auto simp add: ntt_layer_offset_bound ntt_layer_fuel_not_exhausted ring_distribs)
      done
    subgoal \<comment> \<open>Shift bound\<close>
      by crush_base (simp add: min_absorb2 ntt_layer_nb_le_N ntt_layer_total_size_word
          word_of_nat_mult_numeral word_of_nat_mult_numeral_right)
    done
  subgoal \<comment> \<open>Shift amount bound\<close>
    by (simp add: unat_sub word_le_nat_alt)
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_ntt\_c\<close> contract\<close>

text \<open>Forward NTT on a polynomial. Applies 7 NTT layers in-place.
  Requires input coefficients bounded by @{term MLKEM_Q} for overflow safety.\<close>
definition c_mlk_poly_ntt_c_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_ntt_c_contract p gp vp ap \<equiv>
    let pre  = can_alloc_reference \<star>
               p \<mapsto>\<langle>\<top>\<rangle> gp\<down>vp \<star>
               \<langle>refines_mlk_poly vp ap\<rangle> \<star>
               \<langle>coeff_bound MLKEM_Q ap\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gp' vp'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>vp' \<star>
               \<langle>refines_mlk_poly vp' (poly_ntt_int ap)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_ntt_c_contract

lemma c_mlk_poly_ntt_c_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_ntt_c MLKEM_N while_fuel while_fuel MLKEM_N 7 p \<Turnstile>\<^sub>F
            c_mlk_poly_ntt_c_contract p gp vp ap\<close>
  sorry

subsection \<open>\<^verbatim>\<open>mlk\_poly\_ntt\<close> contract\<close>

definition c_mlk_poly_ntt_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_ntt_contract p gp vp ap \<equiv>
    let pre  = can_alloc_reference \<star>
               p \<mapsto>\<langle>\<top>\<rangle> gp\<down>vp \<star>
               \<langle>refines_mlk_poly vp ap\<rangle> \<star>
               \<langle>coeff_bound MLKEM_Q ap\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gp' vp'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>vp' \<star>
               \<langle>refines_mlk_poly vp' (poly_ntt_int ap)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_ntt_contract

lemma c_mlk_poly_ntt_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_ntt 7 MLKEM_N while_fuel while_fuel MLKEM_N p \<Turnstile>\<^sub>F
            c_mlk_poly_ntt_contract p gp vp ap\<close>
  sorry

subsection \<open>\<^verbatim>\<open>mlk\_poly\_invntt\_tomont\_c\<close> contract\<close>

text \<open>Inverse NTT with Montgomery post-scaling. Applies fqmul by 1441
  to all coefficients, then 7 inverse NTT layers.\<close>
definition c_mlk_poly_invntt_tomont_c_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_invntt_tomont_c_contract p gp vp ap \<equiv>
    let pre  = can_alloc_reference \<star>
               p \<mapsto>\<langle>\<top>\<rangle> gp\<down>vp \<star>
               \<langle>refines_mlk_poly vp ap\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gp' vp'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>vp' \<star>
               \<langle>refines_mlk_poly vp' (poly_invntt_tomont_int ap)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_invntt_tomont_c_contract

lemma c_mlk_poly_invntt_tomont_c_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_invntt_tomont_c while_fuel while_fuel while_fuel while_fuel while_fuel while_fuel while_fuel while_fuel p \<Turnstile>\<^sub>F
            c_mlk_poly_invntt_tomont_c_contract p gp vp ap\<close>
  sorry

subsection \<open>\<^verbatim>\<open>mlk\_poly\_invntt\_tomont\<close> contract\<close>

definition c_mlk_poly_invntt_tomont_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_poly_invntt_tomont_contract p gp vp ap \<equiv>
    let pre  = can_alloc_reference \<star>
               p \<mapsto>\<langle>\<top>\<rangle> gp\<down>vp \<star>
               \<langle>refines_mlk_poly vp ap\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gp' vp'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>vp' \<star>
               \<langle>refines_mlk_poly vp' (poly_invntt_tomont_int ap)\<rangle>)
     in make_function_contract pre post\<close>
ucincl_auto c_mlk_poly_invntt_tomont_contract

lemma c_mlk_poly_invntt_tomont_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_invntt_tomont while_fuel while_fuel while_fuel while_fuel while_fuel while_fuel while_fuel while_fuel p \<Turnstile>\<^sub>F
            c_mlk_poly_invntt_tomont_contract p gp vp ap\<close>
  sorry

end

end
