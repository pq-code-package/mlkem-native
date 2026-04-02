(*<*)
theory MLKEM_FC_Montgomery
  imports MLKEM_FC_Scalar
begin
(*>*)

text \<open>
  Functional correctness proofs for Montgomery reduction
  (@{verbatim \<open>mlk_montgomery_reduce\<close>}), field multiplication
  (@{verbatim \<open>mlk_fqmul\<close>}), and the signed-to-unsigned conversion
  (@{verbatim \<open>mlk_scalar_signed_to_unsigned_q\<close>}).
\<close>

section \<open>Montgomery Reduction and Field Multiplication\<close>

(*<*)
context c_mlk_machine_model
begin

declare c_mlk_montgomery_reduce_def [micro_rust_simps del]
declare c_mlk_fqmul_def [micro_rust_simps del]
declare c_mlk_scalar_signed_to_unsigned_q_def [micro_rust_simps del]
(*>*)

subsection \<open>@{text mlk_montgomery_reduce} contract\<close>

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
(*<*)ucincl_auto c_mlk_montgomery_reduce_contract(*>*)

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
    fixes a :: \<open>32 signed word\<close>
      and t :: \<open>16 signed word\<close>
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
    thus ?thesis
      using step1 step2 step3 by simp
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
  define t_w where
    \<open>t_w \<equiv> SCAST(16 \<rightarrow> 16 signed) (UCAST(32 \<rightarrow> 16)
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
    using sub_bounds by (simp add: sint_word_diff word_size signed_take_bit_int_eq_self)
  \<comment> \<open>sint of multiplication t_w * Q\<close>
  have sint_mul: \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) t_w * 0xD01) =
    sint t_w * 3329\<close>
  proof -
    note mul_bounds = montgomery_t_mul_Q_bounds[where t=t_w]
    have \<open>signed_take_bit 31 (sint (SCAST(16 signed \<rightarrow> 32 signed) t_w) * 3329) =
          sint (SCAST(16 signed \<rightarrow> 32 signed) t_w) * 3329\<close>
      using mul_bounds by (intro signed_take_bit_int_eq_self) auto
    thus ?thesis
      by (simp add: sint_word_mult word_size sint_cast)
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
  define r where
    \<open>r = montgomery_reduce_int (sint a)\<close>
  have \<open>sint (SCAST(32 signed \<rightarrow> 16 signed) (word_of_int r :: 32 signed word)) = r\<close>
  proof -
    have \<open>sint (word_of_int r :: 32 signed word) = r\<close>
      using result_bound unfolding r_def by (intro sint_of_int_eq) auto
    hence \<open>SCAST(32 signed \<rightarrow> 16 signed) (word_of_int r :: 32 signed word) =
           (word_of_int r :: 16 signed word)\<close>
      by (simp add: scast_def)
    moreover have \<open>sint (word_of_int r :: 16 signed word) = r\<close>
      using result_bound unfolding r_def by (intro sint_of_int_eq) (auto simp: word_size)
    ultimately show ?thesis
      by simp
  qed
  thus ?thesis
    using div_eq by (simp add: t_w_def r_def)
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

subsection \<open>@{text mlk_fqmul} contract\<close>

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
(*<*)ucincl_auto c_mlk_fqmul_contract(*>*)

lemma c_mlk_fqmul_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_fqmul while_fuel while_fuel a b \<Turnstile>\<^sub>F
            c_mlk_fqmul_contract a b\<close>
  apply (crush_boot f: c_mlk_fqmul_def contract: c_mlk_fqmul_contract_def)
  apply crush_base
  apply (insert fqmul_product_bound[of a b])
  apply (simp_all add: fqmul_sint_product sint_up_scast is_up)
  done

subsection \<open>@{text mlk_scalar_signed_to_unsigned_q} contract\<close>

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
(*<*)ucincl_auto c_mlk_scalar_signed_to_unsigned_q_contract(*>*)

lemma c_mlk_scalar_signed_to_unsigned_q_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_scalar_signed_to_unsigned_q while_fuel c \<Turnstile>\<^sub>F
            c_mlk_scalar_signed_to_unsigned_q_contract c\<close>
  apply (crush_boot f: c_mlk_scalar_signed_to_unsigned_q_def
           contract: c_mlk_scalar_signed_to_unsigned_q_contract_def)
  apply crush_base
  apply (simp_all add: scalar_unsigned_q_cast_sint sint_up_scast is_up)
  done

(*<*)
end
(*>*)

(*<*)
end
(*>*)
