(*<*)
theory MLKEM_FC_InvNTT
  imports MLKEM_FC_NTT MLKEM_InvNTT_Spec
begin
(*>*)

text \<open>
  Functional correctness proof of the inverse NTT implementation.
  Verifies the single-layer and outer-loop functions (including fqmul
  prescaling) against the abstract specification from
  @{text MLKEM_InvNTT_Spec}.
\<close>

section \<open>Inverse NTT Verification\<close>

(*<*)
context c_mlk_machine_model
begin

declare c_mlk_invntt_layer_def [micro_rust_simps del]
declare c_mlk_poly_invntt_tomont_c_def [micro_rust_simps del]
(*>*)

subsection \<open>@{text mlk_invntt_layer} contract\<close>

text \<open>Single inverse NTT layer.  Applies Gentleman--Sande butterflies
  (Barrett-reduced sum, Montgomery-multiplied difference) across all
  blocks at a given stride.\<close>

definition c_mlk_invntt_layer_contract ::
  \<open>('addr, 8 word list, c_short list) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
   c_short list \<Rightarrow> int list \<Rightarrow>
   c_uint \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_invntt_layer_contract r gr cs acs layer_val \<equiv>
    let l    = unat layer_val;
        pre  = can_alloc_reference \<star>
               r \<mapsto>\<langle>\<top>\<rangle> gr\<down>cs \<star>
               \<langle>refines_coeffs cs acs\<rangle> \<star>
               \<langle>1 \<le> l\<rangle> \<star>
               \<langle>l \<le> 7\<rangle> \<star>
               \<langle>coeff_bound MLKEM_Q acs\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
               \<langle>refines_coeffs cs' (invntt_layer_int l acs)\<rangle>)
    in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_invntt_layer_contract(*>*)

text \<open>Helper: the invNTT middle loop step lemma, folding the loop body result back
  to the abstract spec form. Analogous to @{thm ntt_middle_loop_int_step}.\<close>

lemma invntt_middle_loop_int_step:
  shows \<open>invntt_inner_loop_int (zetas_int ! (k - j)) (j * (2 * blen)) blen blen
           (snd (invntt_middle_loop_int k blen j j cs)) =
         snd (invntt_middle_loop_int (k - 1) blen j (Suc j)
           (invntt_inner_loop_int (zetas_int ! k) 0 blen blen cs))\<close>
by (simp add: invntt_middle_loop_int_snoc[symmetric] invntt_middle_loop_int.simps(2) Let_def)

text \<open>Specialization of @{thm invntt_middle_loop_int_step} for the concrete
  zeta index expression arising in the invNTT layer proof.\<close>

lemma invntt_layer_step:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - ko < 2 ^ (l - Suc 0)\<close>
      and \<open>ko \<le> 255\<close>
    shows \<open>invntt_inner_loop_int (zetas_int ! (2 ^ l + ko - MLKEM_N))
             ((255 - ko) * (2 * blen)) blen blen
            (snd (invntt_middle_loop_int (2 ^ l - Suc 0) blen (255 - ko) (255 - ko) cs)) =
           snd (invntt_middle_loop_int (2 ^ l - Suc (Suc 0)) blen (255 - ko) (Suc (255 - ko))
             (invntt_inner_loop_int (zetas_int ! (2 ^ l - Suc 0)) 0 blen blen cs))\<close>
proof -
  from assms have l_cases: \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  hence idx: \<open>2 ^ l + ko - MLKEM_N = (2 ^ l - Suc 0) - (255 - ko)\<close>
    using assms by auto
  have dec: \<open>2 ^ l - Suc (Suc 0) = (2 ^ l - Suc 0) - 1\<close>
    using l_cases by auto
  show ?thesis
    by (simp only: idx dec invntt_middle_loop_int_step)
qed

lemma invntt_layer_k_dec_word:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - ko < 2 ^ (l - Suc 0)\<close>
      and \<open>ko \<le> 255\<close>
    shows \<open>(word_of_nat (2 ^ l - Suc (Suc (255 - ko))) :: 32 word) =
             word_of_nat (2 ^ l + ko - MLKEM_N) - 1\<close>
proof -
  from assms have l_cases: \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  have eq: \<open>2 ^ l - Suc (Suc (255 - ko)) = (2 ^ l + ko - MLKEM_N) - 1\<close>
    using l_cases assms by auto
  show ?thesis
    unfolding eq using l_cases assms by auto
qed

lemma invntt_layer_total_bound:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - ko < 2 ^ (l - Suc 0)\<close>
      and \<open>ko \<le> 255\<close>
    shows \<open>(255 - ko) * (2 * 2 ^ (8 - l)) + 2 * 2 ^ (8 - l) \<le> MLKEM_N\<close>
proof -
  from assms have l_cases: \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by auto
qed

lemma invntt_inner_loop_cond:
  assumes \<open>Suc 0 \<le> l\<close> \<open>l \<le> 7\<close> \<open>255 - ko < 2 ^ (l - Suc 0)\<close> \<open>ko \<le> 255\<close> \<open>k \<le> 255\<close>
    shows \<open>(unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - l)) +
                  word_of_nat (min (255 - k) (2 ^ (8 - l)))) <
            unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - l)) + 2 ^ (8 - l))) =
           (255 - k < 2 ^ (8 - l))\<close>
proof -
  from assms have l_cases: \<open>l \<in> {1,2,3,4,5,6,7}\<close> by auto
  show ?thesis
  proof
    assume cond: \<open>unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - l)) +
                        word_of_nat (min (255 - k) (2 ^ (8 - l)))) <
                  unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - l)) + 2 ^ (8 - l))\<close>
    show \<open>255 - k < 2 ^ (8 - l)\<close>
    proof (rule ccontr)
      assume \<open>\<not> 255 - k < 2 ^ (8 - l)\<close>
      hence \<open>min (255 - k) (2 ^ (8 - l)) = 2 ^ (8 - l)\<close> by (simp add: min_def)
      with cond show False by simp
    qed
  next
    assume cond: \<open>255 - k < 2 ^ (8 - l)\<close>
    show \<open>unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - l)) +
                word_of_nat (min (255 - k) (2 ^ (8 - l)))) <
          unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - l)) + 2 ^ (8 - l))\<close>
      using l_cases assms cond
      by (auto simp del: of_nat_mult of_nat_add of_nat_diff
             simp add: word_of_nat_mult_numeral word_of_nat_mult_numeral_right
                  unat_word_ariths(1) unat_sub word_le_nat_alt unat_of_nat
                  min_def)
  qed
qed

text \<open>Zeta index bound for the inverse NTT: the k variable (starting at @{term \<open>2^l - 1\<close>}
  and decrementing) always stays below 128.\<close>

lemma invntt_layer_k_bound:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
    shows \<open>2 ^ l - Suc 0 - j < (128 :: nat)\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  then show ?thesis
    by auto
qed

lemma invntt_layer_unat_k_index:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - k < 2 ^ (l - Suc 0)\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>unat ((2::32 word) ^ l - 1 - (0xFF - word_of_nat k)) = 2 ^ l - Suc 0 - (255 - k)\<close>
proof -
  from assms have l_cases: \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  have eq0: \<open>(0xFF :: 32 word) - word_of_nat k = word_of_nat (255 - k)\<close>
    using assms(4) by (simp add: of_nat_diff)
  have le: \<open>(255 :: nat) - k \<le> 2 ^ l - 1\<close>
    using l_cases assms(3) by auto
  have eq1: \<open>(2 :: 32 word) ^ l - 1 = word_of_nat (2 ^ l - 1)\<close>
    using l_cases by (elim insertE emptyE; simp)
  have eq2: \<open>word_of_nat (2 ^ l - 1) - word_of_nat (255 - k) =
             (word_of_nat (2 ^ l - 1 - (255 - k)) :: 32 word)\<close>
    by (rule of_nat_diff[OF le, symmetric])
  have bound: \<open>2 ^ l - 1 - (255 - k) < 2 ^ LENGTH(32)\<close>
    using l_cases by auto
  show ?thesis
    unfolding eq0 eq1 eq2 unat_of_nat using bound by (simp add: mod_less)
qed

lemma invntt_layer_zeta_index_bound:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - k < 2 ^ (l - Suc 0)\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>(2 ^ l + k - MLKEM_N) mod 4294967296 < 128\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by auto
qed

lemma invntt_layer_zeta_index_eq:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - k < 2 ^ (l - Suc 0)\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>(2 ^ l + k - MLKEM_N) mod 4294967296 = 2 ^ l - Suc 0 - (255 - k)\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by auto
qed

lemma invntt_layer_zeta_index_bound_raw:
  assumes \<open>Suc 0 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>255 - k < 2 ^ (l - Suc 0)\<close>
      and \<open>k \<le> 255\<close>
    shows \<open>2 ^ l + k - MLKEM_N < 128\<close>
proof -
  from assms have \<open>l \<in> {1,2,3,4,5,6,7}\<close>
    by auto
  with assms show ?thesis
    by auto
qed

lemma coeff_bound_map_sint_update2:
  assumes \<open>coeff_bound B (list.map sint cs)\<close>
      and \<open>\<bar>sint v1\<bar> < B\<close> and \<open>\<bar>sint v2\<bar> < B\<close>
      and \<open>i < length cs\<close> and \<open>j < length cs\<close>
  shows \<open>coeff_bound B (list.map sint (cs[i := v1, j := v2]))\<close>
using assms unfolding coeff_bound_def by (auto simp: nth_list_update)

lemma invntt_unat_idx:
    fixes layer_val :: \<open>32 word\<close>
  assumes \<open>unat layer_val \<le> 7\<close> \<open>Suc 0 \<le> unat layer_val\<close>
      and \<open>ko \<le> 255\<close> \<open>ki \<le> 255\<close>
      and \<open>255 - ki < 2 ^ (8 - unat layer_val)\<close>
      and \<open>(255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + 2 * 2 ^ (8 - unat layer_val) \<le> MLKEM_N\<close>
    shows \<open>unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - unat layer_val))
              + (0xFF - word_of_nat ki)) =
           (255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (255 - ki)\<close>
      and \<open>unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - unat layer_val))
              + (0xFF - word_of_nat ki) + 2 ^ (8 - unat layer_val)) =
           (255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (255 - ki) + 2 ^ (8 - unat layer_val)\<close>
proof -
  have ki_bound: \<open>ki < 2 ^ LENGTH(32)\<close> using assms by simp
  have ko_bound: \<open>ko < 2 ^ LENGTH(32)\<close> using assms by simp
  have ki_le: \<open>word_of_nat ki \<le> (0xFF :: 32 word)\<close>
    using assms ki_bound by (simp add: word_le_nat_alt unat_of_nat mod_less)
  have ko_le: \<open>word_of_nat ko \<le> (0xFF :: 32 word)\<close>
    using assms ko_bound by (simp add: word_le_nat_alt unat_of_nat mod_less)
  have h_ki: \<open>unat (0xFF - word_of_nat ki :: 32 word) = 255 - ki\<close>
    using unat_sub[OF ki_le] ki_bound by (simp add: unat_of_nat)
  have h_mul: \<open>unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - unat layer_val)))
      = (255 - ko) * (2 * 2 ^ (8 - unat layer_val))\<close>
    by (rule ntt_layer_unat_offset[OF assms(2) assms(1) assms(3)])
  have sum_bound: \<open>(255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (255 - ki) < 2 ^ LENGTH(32)\<close>
    using assms by simp
  have sum_bound2: \<open>(255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (255 - ki)
      + 2 ^ (8 - unat layer_val) < 2 ^ LENGTH(32)\<close>
    using assms by simp
  show \<open>unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - unat layer_val))
            + (0xFF - word_of_nat ki)) =
         (255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (255 - ki)\<close>
    using sum_bound by (simp only: unat_word_ariths(1) h_mul h_ki) (simp add: mod_less)
  show \<open>unat ((0xFF - word_of_nat ko :: 32 word) * (2 * 2 ^ (8 - unat layer_val))
            + (0xFF - word_of_nat ki) + 2 ^ (8 - unat layer_val)) =
         (255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (255 - ki) + 2 ^ (8 - unat layer_val)\<close>
    using sum_bound2 by (simp only: unat_word_ariths(1) h_mul h_ki) (simp add: mod_less)
qed

lemma invntt_butterfly_block_fc_step:
    fixes ra :: \<open>c_short list\<close>
      and r_br r_fq :: c_short
      and z :: \<open>int\<close>
      and off blen m :: \<open>nat\<close>
  assumes ra_eq: \<open>list.map sint ra = invntt_inner_loop_int z off blen m base_cs\<close>
      and br_eq: \<open>sint r_br = barrett_reduce_int (sint (ra!(off+m) + ra!(off+m+blen)))\<close>
      and fq_eq: \<open>sint r_fq = fqmul_int (sint (ra!(off+m+blen) - ra!(off+m))) z\<close>
      and m_bound: \<open>m < blen\<close>
      and sum_bound: \<open>off + 2 * blen \<le> MLKEM_N\<close>
      and len_ra: \<open>length ra = MLKEM_N\<close>
      and cb: \<open>coeff_bound MLKEM_Q (list.map sint ra)\<close>
  shows \<open>list.map sint (ra[off+m := r_br, off+m+blen := r_fq]) =
         invntt_inner_loop_int z off blen (Suc m) base_cs\<close>
proof -
  \<comment> \<open>Abstract state after m iterations\<close>
  define L where
    \<open>L = list.map sint ra\<close>
  from m_bound sum_bound len_ra have lo_bound: \<open>off + m < length ra\<close> and hi_bound: \<open>off + m + blen < length ra\<close>
    by auto
  have L_eq: \<open>L = invntt_inner_loop_int z off blen m base_cs\<close>
    using ra_eq L_def by simp
  have L_lo: \<open>L ! (off + m) = sint (ra ! (off + m))\<close>
    using lo_bound L_def by (simp add: nth_map)
  have L_hi: \<open>L ! (off + m + blen) = sint (ra ! (off + m + blen))\<close>
    using hi_bound L_def by (simp add: nth_map)
  \<comment> \<open>Overflow safety from coeff_bound\<close>
  have ob: \<open>- 32768 \<le> L ! (off + m) + L ! (off + m + blen)\<close>
           \<open>L ! (off + m) + L ! (off + m + blen) \<le> 32767\<close>
           \<open>- 32768 \<le> L ! (off + m + blen) - L ! (off + m)\<close>
           \<open>L ! (off + m + blen) - L ! (off + m) \<le> 32767\<close>
    using invntt_coeff_bound_sum_bounds[of L \<open>off + m\<close> blen] cb lo_bound hi_bound by (auto simp: L_def)
  \<comment> \<open>sint distributes over + and -\<close>
  have sint_add: \<open>sint (ra ! (off + m) + ra ! (off + m + blen)) =
                  sint (ra ! (off + m)) + sint (ra ! (off + m + blen))\<close>
    by (rule sint_plus_no_overflow) (use ob L_lo L_hi in auto)
  have sint_sub: \<open>sint (ra ! (off + m + blen) - ra ! (off + m)) =
                  sint (ra ! (off + m + blen)) - sint (ra ! (off + m))\<close>
    by (rule sint_minus_no_overflow) (use ob L_lo L_hi in auto)
  \<comment> \<open>RHS: expand via snoc + butterfly\<close>
  have rhs_eq: \<open>invntt_inner_loop_int z off blen (Suc m) base_cs =
                (L[off + m := barrett_reduce_int (L ! (off + m) + L ! (off + m + blen))])
                 [off + m + blen := fqmul_int (L ! (off + m + blen) - L ! (off + m)) z]\<close>
    unfolding L_eq invntt_inner_loop_int_snoc invntt_butterfly_int_def Let_def by simp
  \<comment> \<open>LHS: push map sint through updates, substitute\<close>
  have lhs_eq: \<open>list.map sint (ra[off + m := r_br, off + m + blen := r_fq]) =
                (L[off + m := sint r_br])[off + m + blen := sint r_fq]\<close>
    using L_def lo_bound hi_bound by (simp add: List.map_update)
  show ?thesis
    using lhs_eq rhs_eq br_eq fq_eq sint_add sint_sub L_lo L_hi by simp
qed

lemma invntt_butterfly_block_fc_step':
    fixes ra :: \<open>c_short list\<close>
      and r_br r_fq :: c_short
      and z :: \<open>int\<close>
      and off blen m :: \<open>nat\<close>
  assumes ra_eq: \<open>list.map sint ra = invntt_inner_loop_int z off blen m base_cs\<close>
      and br_eq: \<open>sint r_br = barrett_reduce_int (sint (ra!(off+m) + ra!(off+m+blen)))\<close>
      and fq_eq: \<open>sint r_fq = fqmul_int (sint (ra!(off+m+blen) - ra!(off+m))) z\<close>
      and m_bound: \<open>m < blen\<close>
      and sum_bound: \<open>off + 2 * blen \<le> MLKEM_N\<close>
      and len_ra: \<open>length ra = MLKEM_N\<close>
      and cb: \<open>coeff_bound MLKEM_Q (list.map sint ra)\<close>
    shows \<open>list.map sint (ra[off+m := r_br, off+m+blen := r_fq]) =
             invntt_inner_loop_int z (Suc off) blen m
               (invntt_butterfly_int z off blen base_cs)\<close>
using invntt_butterfly_block_fc_step[OF assms] by (simp add: invntt_inner_loop_int_snoc)

lemma c_mlk_invntt_layer_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_invntt_layer while_fuel while_fuel while_fuel MLKEM_N MLKEM_N
              r layer_val \<Turnstile>\<^sub>F
            c_mlk_invntt_layer_contract r gr cs acs layer_val\<close>
  apply (crush_boot f: c_mlk_invntt_layer_def
                   contract: c_mlk_invntt_layer_contract_def)
  apply crush_base
  subgoal for x xa xb \<comment> \<open>Main while loop\<close>
    apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>k. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
              \<langle>refines_coeffs cs'
                  (snd (invntt_middle_loop_int (2^(unat layer_val) - 1) (2^(8 - unat layer_val))
                      (min (MLKEM_N - k) (2^(unat layer_val - 1)))
                      (min (MLKEM_N - k) (2^(unat layer_val - 1))) acs))\<rangle>)
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat (min (MLKEM_N - k) (2^(unat layer_val - 1)) * (2 * 2^(8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gk. xa \<mapsto>\<langle>\<top>\<rangle> gk\<down>(of_nat (2^(unat layer_val) - 1 - min (MLKEM_N - k) (2^(unat layer_val - 1))) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2^(8 - unat layer_val)) :: c_uint))
              \<star> can_alloc_reference
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle>  \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>k \<le> MLKEM_N\<rangle>\<close>
          and INV'=\<open>\<lambda>k. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
              \<langle>refines_coeffs cs'
                  (snd (invntt_middle_loop_int (2^(unat layer_val) - 1) (2^(8 - unat layer_val))
                      (MLKEM_N - Suc k) (MLKEM_N - Suc k) acs))\<rangle>)
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat ((MLKEM_N - Suc k) * (2 * 2^(8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gk. xa \<mapsto>\<langle>\<top>\<rangle> gk\<down>(of_nat (2^(unat layer_val) - 1 - (MLKEM_N - Suc k)) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2^(8 - unat layer_val)) :: c_uint))
              \<star> can_alloc_reference
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle>  \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>Suc k \<le> MLKEM_N\<rangle>
              \<star> \<langle>MLKEM_N - Suc k < 2^(unat layer_val - 1)\<rangle>\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
    subgoal \<comment> \<open>Init + Finalization\<close>
      by (crush_base simp add: min_absorb2 invntt_layer_int_def ntt_layer_total_size ntt_layer_nb_le_N
              unat_sub word_le_nat_alt drop_bit_0x100_eq ntt_layer_total_size_word)
    subgoal \<comment> \<open>Condition check\<close>
      by crush_base (simp_all add: ntt_layer_start_cond ntt_layer_cond_false_min
              word_of_nat_255_sub)
    subgoal for ko \<comment> \<open>Loop body\<close>
      \<comment> \<open>Phase 1: VCG without zetas literal\<close>
      apply (crush_base simp add: bind2_unseq_def refines_coeffs_def min_absorb2
          word_less_nat_alt unat_of_nat word_le_nat_alt unat_sub
          invntt_layer_k_bound ntt_layer_total_size ntt_layer_total_size_word
          ntt_layer_nb_le_N
          invntt_middle_loop_int_length invntt_inner_loop_int_length)
      \<comment> \<open>Phase 2: finish VCG with zeta index bounds and folding\<close>
      apply (crush_base simp add:
          c_global_mlk_zetas_def zetas_sword_unfold[symmetric]
          zetas_sword_sint
          invntt_layer_zeta_index_bound invntt_layer_zeta_index_eq
          bind2_unseq_def refines_coeffs_def min_absorb2
          word_less_nat_alt unat_of_nat word_le_nat_alt unat_sub
          invntt_layer_k_bound ntt_layer_total_size ntt_layer_total_size_word
          ntt_layer_nb_le_N
          invntt_middle_loop_int_snoc[symmetric]
          invntt_middle_loop_int_length invntt_inner_loop_int_length)
      \<comment> \<open>Phase 3: rewrite zeta index bound to True\<close>
      apply (simp_all only: invntt_layer_zeta_index_bound_raw)
      \<comment> \<open>4 goals: WP1, Abort1(\<not>True), WP2, Abort2(\<not>True)\<close>
      subgoal for gl0 gr0 gs0 cs0 gk0 xj xz \<comment> \<open>Inner while loop WP1\<close>
        apply (ucincl_discharge\<open>
            rule_tac
              INV=\<open>\<lambda>ki. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
                  \<langle>refines_coeffs cs'
                      (invntt_inner_loop_int (zetas_int ! (2 ^ unat layer_val + ko - MLKEM_N))
                          ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)))
                          (2 ^ (8 - unat layer_val))
                          (min (MLKEM_N - ki) (2 ^ (8 - unat layer_val)))
                          (snd (invntt_middle_loop_int (2 ^ unat layer_val - 1) (2 ^ (8 - unat layer_val))
                              (255 - ko) (255 - ko) (list.map sint cs))))\<rangle>
                  \<star> \<langle>length cs' = MLKEM_N\<rangle>
                  \<star> \<langle>coeff_bound MLKEM_Q (list.map sint cs')\<rangle>)
              \<star> (\<Squnion>gj. xj \<mapsto>\<langle>\<top>\<rangle> gj\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + min (MLKEM_N - ki) (2 ^ (8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2 ^ (8 - unat layer_val)) :: c_uint))
              \<star> (\<Squnion>gz. xz \<mapsto>\<langle>\<top>\<rangle> gz\<down>(zetas_sword ! (2 ^ unat layer_val + ko - MLKEM_N)))
              \<star> can_alloc_reference
              \<star> \<langle>(255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + 2 * 2 ^ (8 - unat layer_val) \<le> MLKEM_N\<rangle>
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle> \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>ko \<le> 255\<rangle> \<star> \<langle>255 - ko < 2 ^ (unat layer_val - Suc 0)\<rangle>
              \<star> \<langle>length cs = MLKEM_N\<rangle>
              \<star> \<langle>ki \<le> MLKEM_N\<rangle>
              \<star> \<langle>coeff_bound MLKEM_Q acs\<rangle>\<close>
            and INV'=\<open>\<lambda>ki. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
                  \<langle>refines_coeffs cs'
                      (invntt_inner_loop_int (zetas_int ! (2 ^ unat layer_val + ko - MLKEM_N))
                          ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)))
                          (2 ^ (8 - unat layer_val))
                          (MLKEM_N - Suc ki)
                          (snd (invntt_middle_loop_int (2 ^ unat layer_val - 1) (2 ^ (8 - unat layer_val))
                              (255 - ko) (255 - ko) (list.map sint cs))))\<rangle>
                  \<star> \<langle>length cs' = MLKEM_N\<rangle>
                  \<star> \<langle>coeff_bound MLKEM_Q (list.map sint cs')\<rangle>)
              \<star> (\<Squnion>gj. xj \<mapsto>\<langle>\<top>\<rangle> gj\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (MLKEM_N - Suc ki)) :: c_uint))
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2 ^ (8 - unat layer_val)) :: c_uint))
              \<star> (\<Squnion>gz. xz \<mapsto>\<langle>\<top>\<rangle> gz\<down>(zetas_sword ! (2 ^ unat layer_val + ko - MLKEM_N)))
              \<star> can_alloc_reference
              \<star> \<langle>(255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + 2 * 2 ^ (8 - unat layer_val) \<le> MLKEM_N\<rangle>
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle> \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>ko \<le> 255\<rangle> \<star> \<langle>255 - ko < 2 ^ (unat layer_val - Suc 0)\<rangle>
              \<star> \<langle>length cs = MLKEM_N\<rangle>
              \<star> \<langle>Suc ki \<le> MLKEM_N\<rangle>
              \<star> \<langle>MLKEM_N - Suc ki < 2 ^ (8 - unat layer_val)\<rangle>
              \<star> \<langle>coeff_bound MLKEM_Q acs\<rangle>\<close>
            and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        subgoal \<comment> \<open>Init + Finalization\<close>
          apply (crush_base simp add: min_absorb2 refines_coeffs_def
              invntt_middle_loop_int_snoc[symmetric]
              invntt_middle_loop_int_length invntt_inner_loop_int_length
              ntt_layer_total_size ntt_layer_total_size_word ntt_layer_nb_le_N
              word_less_nat_alt unat_of_nat word_le_nat_alt unat_sub)
          apply (simp_all add: invntt_layer_step invntt_layer_k_dec_word
              invntt_layer_total_bound ring_distribs
              ntt_layer_total_size ntt_layer_nb_le_N min_absorb2)
          apply (rule invntt_middle_loop_int_coeff_bound[simplified One_nat_def])
          apply auto
          done
        subgoal \<comment> \<open>Condition\<close>
          by (crush_base simp add: word_less_nat_alt unat_of_nat
              refines_coeffs_def invntt_inner_loop_int_snoc
              invntt_butterfly_int_def fqmul_int_def Let_def
              nth_list_update invntt_inner_loop_int_length
              invntt_inner_loop_cond min_absorb2
              word_le_nat_alt unat_sub)
        subgoal \<comment> \<open>Body\<close>
          using [[linarith_split_limit = 40]]
          apply (crush_base simp add: word_less_nat_alt unat_of_nat
              c_mlk_barrett_reduce_contract_def unat_butterfly_idx
              refines_coeffs_def invntt_inner_loop_int_snoc
              invntt_butterfly_int_def fqmul_int_def Let_def
              nth_list_update invntt_inner_loop_int_length
              invntt_coeff_bound_sum_bounds
              min_absorb2 word_le_nat_alt unat_sub
              zetas_sword_sint)
          subgoal \<comment> \<open>OOB r[j]\<close>
            by (simp add: unat_word_ariths unat_of_nat
                word_le_nat_alt word_less_nat_alt unat_sub)
          subgoal \<comment> \<open>OOB r[j+blen]\<close>
            by (simp add: unat_word_ariths unat_of_nat
                word_le_nat_alt word_less_nat_alt unat_sub)
          subgoal \<comment> \<open>coeff_bound 1\<close>
            by (rule coeff_bound_map_sint_update2;
                simp add: barrett_reduce_int_abs_bound
                    fqmul_int_def[symmetric] fqmul_prescale_bound_sint
                    zetas_sword_sint zetas_int_abs_bound
                    invntt_layer_zeta_index_bound_raw)
          subgoal \<comment> \<open>refinement 1\<close>
            apply (simp only: invntt_unat_idx fqmul_int_def[symmetric]
                zetas_sword_sint invntt_layer_zeta_index_bound_raw)
            apply (rule invntt_butterfly_block_fc_step'[unfolded
                invntt_butterfly_int_def Let_def])
            apply (assumption | simp)+
            done
          subgoal \<comment> \<open>coeff_bound 2\<close>
            by (rule coeff_bound_map_sint_update2;
                simp add: barrett_reduce_int_abs_bound
                    fqmul_int_def[symmetric] fqmul_prescale_bound_sint
                    zetas_sword_sint zetas_int_abs_bound
                    invntt_layer_zeta_index_bound_raw)
          subgoal \<comment> \<open>refinement 2\<close>
            apply (simp only: invntt_unat_idx fqmul_int_def[symmetric]
                zetas_sword_sint invntt_layer_zeta_index_bound_raw)
            apply (rule invntt_butterfly_block_fc_step'[unfolded
                invntt_butterfly_int_def Let_def])
            apply (assumption | simp)+
            done
          done
        subgoal
          by (crush_base simp add: min_absorb2) \<comment> \<open>Fuel\<close>
      done
      subgoal
        by simp \<comment> \<open>Abort1\<close>
      subgoal for gl1 gr1 gs1 cs1 gk1 xj1 xz1 \<comment> \<open>Inner while loop WP2\<close>
        apply (ucincl_discharge\<open>
            rule_tac
              INV=\<open>\<lambda>ki. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
                  \<langle>refines_coeffs cs'
                      (invntt_inner_loop_int (zetas_int ! (2 ^ unat layer_val + ko - MLKEM_N))
                          ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)))
                          (2 ^ (8 - unat layer_val))
                          (min (MLKEM_N - ki) (2 ^ (8 - unat layer_val)))
                          (snd (invntt_middle_loop_int (2 ^ unat layer_val - 1) (2 ^ (8 - unat layer_val))
                              (255 - ko) (255 - ko) (list.map sint cs))))\<rangle>
                  \<star> \<langle>length cs' = MLKEM_N\<rangle>
                  \<star> \<langle>coeff_bound MLKEM_Q (list.map sint cs')\<rangle>)
              \<star> (\<Squnion>gj. xj1 \<mapsto>\<langle>\<top>\<rangle> gj\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + min (MLKEM_N - ki) (2 ^ (8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2 ^ (8 - unat layer_val)) :: c_uint))
              \<star> (\<Squnion>gz. xz1 \<mapsto>\<langle>\<top>\<rangle> gz\<down>(zetas_sword ! (2 ^ unat layer_val + ko - MLKEM_N)))
              \<star> can_alloc_reference
              \<star> \<langle>(255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + 2 * 2 ^ (8 - unat layer_val) \<le> MLKEM_N\<rangle>
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle> \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>ko \<le> 255\<rangle> \<star> \<langle>255 - ko < 2 ^ (unat layer_val - Suc 0)\<rangle>
              \<star> \<langle>length cs = MLKEM_N\<rangle>
              \<star> \<langle>ki \<le> MLKEM_N\<rangle>
              \<star> \<langle>coeff_bound MLKEM_Q acs\<rangle>\<close>
            and INV'=\<open>\<lambda>ki. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
                  \<langle>refines_coeffs cs'
                      (invntt_inner_loop_int (zetas_int ! (2 ^ unat layer_val + ko - MLKEM_N))
                          ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)))
                          (2 ^ (8 - unat layer_val))
                          (MLKEM_N - Suc ki)
                          (snd (invntt_middle_loop_int (2 ^ unat layer_val - 1) (2 ^ (8 - unat layer_val))
                              (255 - ko) (255 - ko) (list.map sint cs))))\<rangle>
                  \<star> \<langle>length cs' = MLKEM_N\<rangle>
                  \<star> \<langle>coeff_bound MLKEM_Q (list.map sint cs')\<rangle>)
              \<star> (\<Squnion>gj. xj1 \<mapsto>\<langle>\<top>\<rangle> gj\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + (MLKEM_N - Suc ki)) :: c_uint))
              \<star> (\<Squnion>gs. x \<mapsto>\<langle>\<top>\<rangle> gs\<down>(of_nat ((255 - ko) * (2 * 2 ^ (8 - unat layer_val))) :: c_uint))
              \<star> (\<Squnion>gl. xb \<mapsto>\<langle>\<top>\<rangle> gl\<down>(of_nat (2 ^ (8 - unat layer_val)) :: c_uint))
              \<star> (\<Squnion>gz. xz1 \<mapsto>\<langle>\<top>\<rangle> gz\<down>(zetas_sword ! (2 ^ unat layer_val + ko - MLKEM_N)))
              \<star> can_alloc_reference
              \<star> \<langle>(255 - ko) * (2 * 2 ^ (8 - unat layer_val)) + 2 * 2 ^ (8 - unat layer_val) \<le> MLKEM_N\<rangle>
              \<star> \<langle>Suc 0 \<le> unat layer_val\<rangle> \<star> \<langle>unat layer_val \<le> 7\<rangle>
              \<star> \<langle>ko \<le> 255\<rangle> \<star> \<langle>255 - ko < 2 ^ (unat layer_val - Suc 0)\<rangle>
              \<star> \<langle>length cs = MLKEM_N\<rangle>
              \<star> \<langle>Suc ki \<le> MLKEM_N\<rangle>
              \<star> \<langle>MLKEM_N - Suc ki < 2 ^ (8 - unat layer_val)\<rangle>
              \<star> \<langle>coeff_bound MLKEM_Q acs\<rangle>\<close>
            and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          in wp_bounded_while_framedI\<close>)
        subgoal \<comment> \<open>Init + Finalization\<close>
          apply (crush_base simp add: min_absorb2 refines_coeffs_def
              invntt_middle_loop_int_snoc[symmetric]
              invntt_middle_loop_int_length invntt_inner_loop_int_length
              ntt_layer_total_size ntt_layer_total_size_word ntt_layer_nb_le_N
              word_less_nat_alt unat_of_nat word_le_nat_alt unat_sub)
          apply (simp_all add: invntt_layer_step invntt_layer_k_dec_word
              invntt_layer_total_bound ring_distribs
              ntt_layer_total_size ntt_layer_nb_le_N min_absorb2)
          apply (rule invntt_middle_loop_int_coeff_bound[simplified One_nat_def])
          apply auto
          done
        subgoal \<comment> \<open>Condition\<close>
          by (crush_base simp add: word_less_nat_alt unat_of_nat
              refines_coeffs_def invntt_inner_loop_int_snoc
              invntt_butterfly_int_def fqmul_int_def Let_def
              nth_list_update invntt_inner_loop_int_length
              invntt_inner_loop_cond min_absorb2
              word_le_nat_alt unat_sub)
        subgoal \<comment> \<open>Body\<close>
          using [[linarith_split_limit = 40]]
          apply (crush_base simp add: word_less_nat_alt unat_of_nat
              c_mlk_barrett_reduce_contract_def unat_butterfly_idx
              refines_coeffs_def invntt_inner_loop_int_snoc
              invntt_butterfly_int_def fqmul_int_def Let_def
              nth_list_update invntt_inner_loop_int_length
              invntt_coeff_bound_sum_bounds
              min_absorb2 word_le_nat_alt unat_sub
              zetas_sword_sint)
          subgoal \<comment> \<open>OOB r[j]\<close>
            by (simp add: unat_word_ariths unat_of_nat
                word_le_nat_alt word_less_nat_alt unat_sub)
          subgoal \<comment> \<open>OOB r[j+blen]\<close>
            by (simp add: unat_word_ariths unat_of_nat
                word_le_nat_alt word_less_nat_alt unat_sub)
          subgoal \<comment> \<open>coeff_bound 1\<close>
            by (rule coeff_bound_map_sint_update2;
                simp add: barrett_reduce_int_abs_bound
                    fqmul_int_def[symmetric] fqmul_prescale_bound_sint
                    zetas_sword_sint zetas_int_abs_bound
                    invntt_layer_zeta_index_bound_raw)
          subgoal \<comment> \<open>refinement 1\<close>
            apply (simp only: invntt_unat_idx fqmul_int_def[symmetric]
                zetas_sword_sint invntt_layer_zeta_index_bound_raw)
            apply (rule invntt_butterfly_block_fc_step'[unfolded
                invntt_butterfly_int_def Let_def])
            apply (assumption | simp)+
            done
          subgoal \<comment> \<open>coeff_bound 2\<close>
            by (rule coeff_bound_map_sint_update2;
                simp add: barrett_reduce_int_abs_bound
                    fqmul_int_def[symmetric] fqmul_prescale_bound_sint
                    zetas_sword_sint zetas_int_abs_bound
                    invntt_layer_zeta_index_bound_raw)
          subgoal \<comment> \<open>refinement 2\<close>
            apply (simp only: invntt_unat_idx fqmul_int_def[symmetric]
                zetas_sword_sint invntt_layer_zeta_index_bound_raw)
            apply (rule invntt_butterfly_block_fc_step'[unfolded
                invntt_butterfly_int_def Let_def])
            apply (assumption | simp)+
            done
          done
        subgoal
          by (crush_base simp add: min_absorb2) \<comment> \<open>Fuel\<close>
        done
      subgoal
        by simp \<comment> \<open>Abort2\<close>
      done
    subgoal \<comment> \<open>Fuel exhaust\<close>
      by (crush_base simp add: min_absorb2 ntt_layer_nb_le_N ntt_layer_total_size_word)
    done
  done

text \<open>Lifted invntt\_layer contract: operates on the poly reference directly.\<close>

definition c_mlk_invntt_layer_poly_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
   c_mlk_poly \<Rightarrow> int list \<Rightarrow> c_uint \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_invntt_layer_poly_contract p gp vp acs layer_val \<equiv>
    let l    = unat layer_val;
        pre  = can_alloc_reference \<star>
               p \<mapsto>\<langle>\<top>\<rangle> gp\<down>vp \<star>
               \<langle>refines_coeffs (c_mlk_poly_coeffs vp) acs\<rangle> \<star>
               \<langle>1 \<le> l\<rangle> \<star>
               \<langle>l \<le> 7\<rangle> \<star>
               \<langle>coeff_bound MLKEM_Q acs\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
               \<langle>refines_coeffs cs' (invntt_layer_int l acs)\<rangle>)
    in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_invntt_layer_poly_contract(*>*)

lemma c_mlk_invntt_layer_poly_spec:
  shows \<open>\<Gamma>; c_mlk_invntt_layer while_fuel while_fuel while_fuel MLKEM_N MLKEM_N
              (focus_reference (Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify
                 c_mlk_poly_coeffs update_c_mlk_poly_coeffs))) p) layer_val \<Turnstile>\<^sub>F
            c_mlk_invntt_layer_poly_contract p gp vp acs layer_val\<close>
  apply (rule satisfies_function_contract_weaken[OF c_mlk_invntt_layer_spec[where
      gr=gp and cs=\<open>c_mlk_poly_coeffs vp\<close> and acs=acs]])
  apply (simp_all add: c_mlk_invntt_layer_poly_contract_def c_mlk_invntt_layer_contract_def Let_def)
  subgoal
    by crush_base
  subgoal
    by crush_base
  subgoal
    by (crush_base intro: focusedR_c_mlk_poly_aentails)
  subgoal
    apply (rule asepconj_mono)
    apply (rule aexists_entailsL)+
    apply (rule aentails_intro(7))+
    apply (rule asepconj_mono2[OF focusedL_c_mlk_poly_aentails])
    done
  apply (rule aentails_refl)
  done

text \<open>Helper lemmas for inverse NTT layer.\<close>

lemma invntt_outer_loop_int_step:
  shows \<open>invntt_outer_loop_int (Suc n) cs =
         invntt_outer_loop_int n (invntt_layer_int (Suc n) cs)\<close>
by (simp add: invntt_layer_int_def Let_def case_prod_beta)

lemma invntt_outer_loop_int_step':
  assumes \<open>l \<ge> 1\<close>
    shows \<open>invntt_outer_loop_int l cs = invntt_outer_loop_int (l - 1) (invntt_layer_int l cs)\<close>
proof -
  from assms obtain n where \<open>l = Suc n\<close>
    using Suc_le_D by auto
  then show ?thesis
    using invntt_outer_loop_int_step by simp
qed

subsection \<open>@{text mlk_poly_invntt_tomont_c} contract\<close>

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
(*<*)ucincl_auto c_mlk_poly_invntt_tomont_c_contract(*>*)

lemma c_mlk_poly_invntt_tomont_c_spec [crush_specs]:
  notes focusedL_c_mlk_poly[crush_aentails_cond_crules, crush_points_to_cond_crules]
  shows \<open>\<Gamma>; c_mlk_poly_invntt_tomont_c MLKEM_N MLKEM_N while_fuel while_fuel while_fuel
              while_fuel while_fuel MLKEM_N p \<Turnstile>\<^sub>F
            c_mlk_poly_invntt_tomont_c_contract p gp vp ap\<close>
  apply (crush_boot f: c_mlk_poly_invntt_tomont_c_def contract: c_mlk_poly_invntt_tomont_c_contract_def)
  apply (crush_base simp add: c_mlk_fqmul_contract_def fqmul_int_def)
  subgoal for x xa xb \<comment> \<open>x=j ref, xa=layer ref, xb=f ref\<close>
    \<comment> \<open>Phase 1: fqmul prescaling by 1441\<close>
    apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>k. (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
              \<langle>length cs' = MLKEM_N\<rangle> \<star>
              \<langle>\<forall>j < MLKEM_N - k. sint (cs' ! j) = fqmul_int (ap ! j) 1441\<rangle> \<star>
              \<langle>\<forall>j. MLKEM_N - k \<le> j \<longrightarrow> j < MLKEM_N \<longrightarrow>
                  cs' ! j = c_mlk_poly_coeffs vp ! j\<rangle>)
              \<star> (\<Squnion>gf. xb \<mapsto>\<langle>\<top>\<rangle> gf\<down>(0x5A1 :: c_short))
              \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - k) :: c_uint))
              \<star> (\<Squnion>gl. xa \<mapsto>\<langle>\<top>\<rangle> gl\<down>(c_uninitialized :: c_uint))
              \<star> can_alloc_reference
              \<star> \<langle>refines_mlk_poly vp ap\<rangle>\<close>
          and INV'=\<open>\<lambda>k. (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
              \<langle>length cs' = MLKEM_N\<rangle> \<star>
              \<langle>\<forall>j < MLKEM_N - Suc k. sint (cs' ! j) = fqmul_int (ap ! j) 1441\<rangle> \<star>
              \<langle>\<forall>j. MLKEM_N - Suc k \<le> j \<longrightarrow> j < MLKEM_N \<longrightarrow>
                  cs' ! j = c_mlk_poly_coeffs vp ! j\<rangle>)
              \<star> (\<Squnion>gf. xb \<mapsto>\<langle>\<top>\<rangle> gf\<down>(0x5A1 :: c_short))
              \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (MLKEM_N - Suc k) :: c_uint))
              \<star> (\<Squnion>gl. xa \<mapsto>\<langle>\<top>\<rangle> gl\<down>(c_uninitialized :: c_uint))
              \<star> can_alloc_reference
              \<star> \<langle>refines_mlk_poly vp ap\<rangle>\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
    subgoal \<comment> \<open>Init + Finalization\<close>
      apply (crush_base simp add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
          c_mlk_poly.record_simps nth_append nth_list_update refines_mlk_poly_def
          fqmul_int_def c_mlk_fqmul_contract_def)
      \<comment> \<open>After fqmul finalization, process layer = 7, then layer while loop\<close>
      subgoal
        apply (ucincl_discharge\<open>
            rule_tac
              INV=\<open>\<lambda>k. (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
                  \<langle>length cs' = MLKEM_N\<rangle> \<star>
                  \<langle>invntt_outer_loop_int (k + 7 - MLKEM_N)
                      (list.map sint cs') = poly_invntt_tomont_int ap\<rangle> \<star>
                  \<langle>coeff_bound MLKEM_Q (list.map sint cs')\<rangle>)
                  \<star> (\<Squnion>gx. xa \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (k + 7 - MLKEM_N) :: c_uint))
                  \<star> can_alloc_reference\<close>
              and INV'=\<open>\<lambda>k. (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
                  \<langle>length cs' = MLKEM_N\<rangle> \<star>
                  \<langle>invntt_outer_loop_int (Suc k + 7 - MLKEM_N)
                      (list.map sint cs') = poly_invntt_tomont_int ap\<rangle> \<star>
                  \<langle>coeff_bound MLKEM_Q (list.map sint cs')\<rangle>)
                  \<star> (\<Squnion>gx. xa \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (Suc k + 7 - MLKEM_N) :: c_uint))
                  \<star> can_alloc_reference
                  \<star> \<langle>1 \<le> Suc k + 7 - MLKEM_N \<and> Suc k + 7 - MLKEM_N \<le> 7\<rangle>\<close>
              and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
              and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
            in wp_bounded_while_framedI\<close>)
        subgoal \<comment> \<open>Init + Finalization of layer loop\<close>
          apply (crush_base simp add: poly_invntt_tomont_int_def refines_mlk_poly_def
              c_mlk_poly.collapse[symmetric] points_to_def
              c_signed_truthy_zero bounded_while_literal_false)
          subgoal
            apply (simp add: coeff_bound_def)
            by (auto simp add: fqmul_int_def intro: fqmul_prescale_bound_sint[where b=1441, simplified])
          subgoal
            apply (rule arg_cong[where f=\<open>invntt_outer_loop_int 7\<close>])
            by (auto intro!: nth_equalityI simp add: fqmul_int_def)
          done
        subgoal \<comment> \<open>Condition check\<close>
          by crush_base (auto simp add: word_le_nat_alt unat_of_nat unat_sub_if_size word_less_nat_alt)
        subgoal for k \<comment> \<open>Loop body\<close>
          apply (crush_base no_schematics)
          apply (ucincl_discharge \<open>rule wp_callI[OF dereference_spec]\<close>)
          apply (force simp add: dereference_contract_def)
          apply (crush_base no_schematics simp add: dereference_contract_def)
          apply (ucincl_discharge \<open>rule wp_callI[OF c_mlk_invntt_layer_poly_spec]\<close>)
          apply (force simp add: c_mlk_invntt_layer_poly_contract_def Let_def c_mlk_poly.sel
              refines_coeffs_def unat_of_nat coeff_bound_def)
          apply (crush_base no_schematics simp add: c_mlk_invntt_layer_poly_contract_def)
          \<comment> \<open>Close pure goals from invntt_layer precondition\<close>
          apply (auto simp add: unat_of_nat word_less_nat_alt unat_sub_if_size word_size
              invntt_outer_loop_int_step' refines_coeffs_def invntt_layer_int_length
              intro: invntt_layer_int_coeff_bound)[4]
          \<comment> \<open>Process dereference+update for layer counter decrement\<close>
          apply crush_base
          by (auto simp add: unat_of_nat word_less_nat_alt unat_sub_if_size word_size
              invntt_outer_loop_int_step' refines_coeffs_def invntt_layer_int_length
              intro: invntt_layer_int_coeff_bound)
        subgoal \<comment> \<open>Fuel exhaust\<close>
          by crush_base
        done
      done
    \<comment> \<open>Condition\<close>
    subgoal
      by (crush_base simp add: word_less_nat_alt unat_of_nat
          c_signed_truthy_zero bounded_while_literal_false)
    \<comment> \<open>Body\<close>
    subgoal for k
      by (crush_base simp add: word_less_nat_alt unat_sub word_le_nat_alt unat_of_nat
          c_mlk_poly.record_simps nth_append nth_list_update refines_mlk_poly_def
          fqmul_int_def c_mlk_fqmul_contract_def
          c_signed_truthy_zero bounded_while_literal_false)
    \<comment> \<open>Fuel exhaust\<close>
    subgoal
      by (crush_base simp add: word_less_nat_alt unat_of_nat
          c_signed_truthy_zero bounded_while_literal_false)
    done
  done

subsection \<open>@{text mlk_poly_invntt_tomont} contract\<close>

text \<open>Top-level wrapper: delegates to @{verbatim \<open>mlk_poly_invntt_tomont_c\<close>}
  via the @{const refines_mlk_poly} abstraction boundary.\<close>

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
(*<*)ucincl_auto c_mlk_poly_invntt_tomont_contract(*>*)

lemma c_mlk_poly_invntt_tomont_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_invntt_tomont MLKEM_N while_fuel while_fuel while_fuel while_fuel
              while_fuel MLKEM_N MLKEM_N p \<Turnstile>\<^sub>F
            c_mlk_poly_invntt_tomont_contract p gp vp ap\<close>
  apply (crush_boot f: c_mlk_poly_invntt_tomont_def contract: c_mlk_poly_invntt_tomont_contract_def)
  apply (rule wp_callI[OF c_mlk_poly_invntt_tomont_c_spec[where gp=gp and vp=vp and ap=ap]])
  apply (simp add: c_mlk_poly_invntt_tomont_c_contract_def)
  apply (crush_base simp add: c_mlk_poly_invntt_tomont_c_contract_def)
  done

(*<*)
end
(*>*)

(*<*)
end
(*>*)
