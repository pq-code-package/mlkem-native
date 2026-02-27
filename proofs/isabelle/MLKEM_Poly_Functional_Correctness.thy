theory MLKEM_Poly_Functional_Correctness
  imports Common MLKEM_Poly_Definitions
begin

section \<open>C verification (source-driven translation)\<close>

context c_mlk_machine_model
begin

subsection \<open>\<^verbatim>\<open>mlk\_barrett\_reduce\<close> contract\<close>

definition c_mlk_barrett_reduce_contract :: \<open>c_short \<Rightarrow> ('s::{sepalg}, c_short, 'b) function_contract\<close> where
  \<open>c_mlk_barrett_reduce_contract a \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>sint r mod MLKEM_Q = sint a mod MLKEM_Q\<rangle>
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

lemma c_mlk_barrett_reduce_spec:
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
  apply (simp add: barrett_result_sint mod_diff_right_eq[symmetric])
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_add\<close> contract\<close>

text \<open>
  The contract is self-contained: refinement, well-formedness, and
  no-overflow are all expressed as pure assertions in the precondition.
  The postcondition asserts the result refines the abstract polynomial sum.
  No external assumptions needed on the specification theorem.
\<close>
definition c_mlk_poly_add_contract :: \<open>('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow>
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
  done

subsection \<open>\<^verbatim>\<open>mlk\_poly\_sub\<close> contract\<close>

definition c_mlk_poly_sub_contract :: \<open>('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow>
      c_mlk_poly \<Rightarrow> int_poly \<Rightarrow> ('addr, 'gv, c_mlk_poly) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_mlk_poly \<Rightarrow>
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
  done

end

end
