(*<*)
theory MLKEM_FC_Scalar
  imports MLKEM_Refinement
begin
(*>*)

text \<open>
  Functional correctness proofs for scalar C helper functions from
  @{verbatim \<open>poly.c\<close>}: Barrett reduction, cast helpers, constant-time
  primitives, and polynomial addition/subtraction.  Each function is
  verified against its abstract specification from @{text MLKEM_Spec}
  and @{text MLKEM_Refinement}.
\<close>

section \<open>Scalar C Verification\<close>

(*<*)
context c_mlk_machine_model
begin

declare c_mlk_cast_uint16_to_int16_def [micro_rust_simps del]
declare c_mlk_cast_int16_to_uint16_def [micro_rust_simps del]
declare c_mlk_ct_cmask_neg_i16_def [micro_rust_simps del]
declare c_mlk_ct_cmask_nonzero_u16_def [micro_rust_simps del]
declare nondet_choice_def [micro_rust_simps del]
declare bind2_unseq_def [micro_rust_simps del]
declare c_mlk_ct_sel_int16_def [micro_rust_simps del]
declare c_mlk_barrett_reduce_def [micro_rust_simps del]
declare c_mlk_value_barrier_i32_def [micro_rust_simps del]
declare c_mlk_cast_int32_to_uint16_def [micro_rust_simps del]
(*>*)

subsection \<open>@{text mlk_barrett_reduce} contract\<close>

text \<open>The C implementation of Barrett reduction is verified against
  @{const barrett_reduce_int} from @{text MLKEM_Spec}.  The contract
  guarantees that the result equals the abstract specification at the
  @{const sint} level.\<close>

definition c_mlk_barrett_reduce_contract :: \<open>c_short \<Rightarrow> ('s::{sepalg}, c_short, 'b) function_contract\<close> where
  \<open>c_mlk_barrett_reduce_contract a \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>sint r = barrett_reduce_int (sint a)\<rangle>
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_barrett_reduce_contract(*>*)

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

(*<*)
lemma bounded_while_literal_false [micro_rust_simps]:
  shows \<open>bounded_while n (\<up>False) body = \<up>()\<close>
by (induction n) (simp_all add: micro_rust_simps)

lemma c_signed_truthy_zero [micro_rust_simps]:
  shows \<open>c_signed_truthy 0 = \<up>False\<close>
by (simp add: c_signed_truthy_def)
(*>*)

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
  apply (simp_all add: barrett_result_sint barrett_reduce_int_def)
  done

subsection \<open>@{text mlk_poly_add} contract\<close>

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
(*<*)ucincl_auto c_mlk_poly_add_contract(*>*)

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

subsection \<open>@{text mlk_poly_sub} contract\<close>

text \<open>Coefficient-wise subtraction, symmetric to @{text poly_add} above.
  Each output coefficient satisfies
  @{text "r!i = a!i - b!i"} at the integer level.\<close>

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
(*<*)ucincl_auto c_mlk_poly_sub_contract(*>*)

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

subsection \<open>@{text mlk_value_barrier_i32} — identity (opt-blocker simplified to 0)\<close>

text \<open>After preprocessing with @{verbatim "mlk_ct_get_optblocker_i32() = 0"},
  the value barrier reduces to @{term \<open>b XOR 0 = b\<close>}.\<close>

definition c_mlk_value_barrier_i32_contract ::
  \<open>c_int \<Rightarrow> ('s::{sepalg}, c_int, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_value_barrier_i32_contract b \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = b\<rangle>
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_value_barrier_i32_contract(*>*)

lemma c_mlk_value_barrier_i32_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_value_barrier_i32 b \<Turnstile>\<^sub>F
            c_mlk_value_barrier_i32_contract b\<close>
  by (crush_boot f: c_mlk_value_barrier_i32_def
        contract: c_mlk_value_barrier_i32_contract_def) crush_base

subsection \<open>@{text mlk_cast_int32_to_uint16}\<close>

text \<open>Truncation cast from 32-bit signed to 16-bit unsigned,
  masking with @{text "0xFFFF"}.  Used throughout the NTT and
  reduction routines to narrow intermediate 32-bit results
  back to coefficient width.\<close>

definition c_mlk_cast_int32_to_uint16_contract ::
  \<open>c_int \<Rightarrow> ('s::{sepalg}, c_ushort, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_cast_int32_to_uint16_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = ucast (x AND 0xFFFF)\<rangle>
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_cast_int32_to_uint16_contract(*>*)

lemma c_mlk_cast_int32_to_uint16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_cast_int32_to_uint16 x \<Turnstile>\<^sub>F
            c_mlk_cast_int32_to_uint16_contract x\<close>
  by (crush_boot f: c_mlk_cast_int32_to_uint16_def
        contract: c_mlk_cast_int32_to_uint16_contract_def)
     (crush_base simp add: scast_ucast_down_same)

subsection \<open>@{text mlk_cast_uint16_to_int16}\<close>

text \<open>Bit-pattern-preserving reinterpretation from unsigned to signed
  16-bit.  The postcondition is simply @{text "r = scast x"}.\<close>

definition c_mlk_cast_uint16_to_int16_contract :: \<open>c_ushort \<Rightarrow>
        ('s::{sepalg}, c_short, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_cast_uint16_to_int16_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = scast x\<rangle>
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_cast_uint16_to_int16_contract(*>*)

lemma c_mlk_cast_uint16_to_int16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_cast_uint16_to_int16 x \<Turnstile>\<^sub>F
            c_mlk_cast_uint16_to_int16_contract x\<close>
  by (crush_boot f: c_mlk_cast_uint16_to_int16_def
        contract: c_mlk_cast_uint16_to_int16_contract_def) crush_base

subsection \<open>@{text mlk_ct_cmask_neg_i16} — negative mask\<close>

text \<open>Returns @{term \<open>0xFFFF :: c_ushort\<close>} when @{term \<open>sint x < 0\<close>},
  @{term \<open>0 :: c_ushort\<close>} otherwise.
  Implements: @{term \<open>(int32_t)x >> 16\<close>} after value-barrier identity.\<close>

definition c_mlk_ct_cmask_neg_i16_contract :: \<open>c_short \<Rightarrow>
        ('s::{sepalg}, c_ushort, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ct_cmask_neg_i16_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = (if sint x < 0 then 0xFFFF else 0)\<rangle>
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_ct_cmask_neg_i16_contract(*>*)

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

subsection \<open>@{text mlk_cast_int16_to_uint16}\<close>

text \<open>Bit-pattern-preserving reinterpretation from signed 32-bit to
  unsigned 16-bit via masking and @{const ucast}.\<close>

definition c_mlk_cast_int16_to_uint16_contract :: \<open>c_int \<Rightarrow>
        ('s::{sepalg}, c_ushort, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_cast_int16_to_uint16_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = ucast x\<rangle>
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_cast_int16_to_uint16_contract(*>*)

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

subsection \<open>@{text mlk_ct_cmask_nonzero_u16} — nonzero mask\<close>

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
(*<*)ucincl_auto c_mlk_ct_cmask_nonzero_u16_contract(*>*)

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

subsection \<open>@{text mlk_ct_sel_int16} — conditional select\<close>

text \<open>Branch-free conditional select: returns @{term \<open>a\<close>} when
  @{term \<open>cond \<noteq> 0\<close>} and @{term \<open>b\<close>} otherwise, using XOR-and-mask
  rather than a conditional branch.  The proof requires several
  word-level cast round-trip lemmas and a bitwise identity showing
  that @{text "b XOR (0xFFFF AND (a XOR b)) = a"}.\<close>
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
    thus ?thesis
      by (simp add: nth_ucast nth_scast word_size is_up is_down)
  next
    case False
    with n16 have \<open>n = 15\<close>
      by linarith
    thus ?thesis
      by (simp add: nth_ucast nth_scast word_size is_up is_down)
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
    hence n16: \<open>n < 16\<close>
      by (simp add: word_size)
    show \<open>?lhs !! n = a !! n\<close>
    proof (cases \<open>n < 15\<close>)
      case True
      thus ?thesis
        by (auto simp add: word_ops_nth_size word_size nth_ucast nth_scast is_up is_down nth_mask)
    next
      case False
      with n16 have \<open>n = 15\<close>
        by linarith
      thus ?thesis
        by (auto simp add: word_ops_nth_size word_size nth_ucast nth_scast is_up is_down nth_mask)
    qed
  qed
qed

text \<open>Returns @{term \<open>a\<close>} when @{term \<open>cond \<noteq> 0\<close>}, @{term \<open>b\<close>} otherwise.\<close>
definition c_mlk_ct_sel_int16_contract :: \<open>c_short \<Rightarrow> c_short \<Rightarrow> c_ushort \<Rightarrow>
      ('s::{sepalg}, c_short, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ct_sel_int16_contract a b cond \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = (if cond \<noteq> 0 then a else b)\<rangle>
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_ct_sel_int16_contract(*>*)

lemma c_mlk_ct_sel_int16_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_ct_sel_int16 a b cond \<Turnstile>\<^sub>F
            c_mlk_ct_sel_int16_contract a b cond\<close>
  apply (crush_boot f: c_mlk_ct_sel_int16_def
           contract: c_mlk_ct_sel_int16_contract_def)
  apply crush_base
  apply (simp_all add: ct_sel_cast_roundtrip ct_sel_xor_identity)
  done

(*<*)
end

end
(*>*)
