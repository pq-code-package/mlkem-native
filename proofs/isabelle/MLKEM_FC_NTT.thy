(*<*)
theory MLKEM_FC_NTT
  imports MLKEM_FC_Montgomery MLKEM_NTT_Spec
begin
(*>*)

text \<open>
  Functional correctness proof of the forward NTT implementation.
  Verifies the butterfly block, single-layer, and outer-loop functions
  against the abstract NTT specification from @{text MLKEM_NTT_Spec}.
\<close>

section \<open>Forward NTT Verification\<close>

(*<*)
context c_mlk_machine_model
begin

declare c_mlk_ntt_butterfly_block_def [micro_rust_simps del]
declare c_mlk_ntt_layer_def [micro_rust_simps del]
declare c_mlk_poly_ntt_c_def [micro_rust_simps del]
declare c_global_mlk_zetas_def [micro_rust_simps del]
(*>*)

subsection \<open>@{text mlk_ntt_butterfly_block} contract\<close>

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
               \<langle>blen \<le> n\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
               \<langle>refines_coeffs cs'
                  (ntt_inner_loop_int (sint zeta) off blen blen acs)\<rangle>)
     in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_ntt_butterfly_block_contract(*>*)

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
  define m where
    \<open>m = n - Suc k\<close>
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
            \<star> \<langle>k \<le> n\<rangle>\<close>
        and INV'=\<open>\<lambda>k. (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
            \<langle>refines_coeffs cs'
                (ntt_inner_loop_int (sint zeta) (unat start_v) (unat len_v)
                    (n - Suc k) acs)\<rangle>)
            \<star> (\<Squnion>gj. x \<mapsto>\<langle>\<top>\<rangle> gj\<down>(of_nat (unat start_v + (n - Suc k)) :: c_uint))
            \<star> can_alloc_reference
            \<star> \<langle>ntt_inner_no_overflow (sint zeta) (unat start_v) (unat len_v) (unat len_v) acs\<rangle>
            \<star> \<langle>unat start_v + 2 * unat len_v \<le> MLKEM_N\<rangle>
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

subsection \<open>@{text mlk_ntt_layer} contract\<close>

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
               \<langle>1 \<le> l\<rangle> \<star>
               \<langle>l \<le> 7\<rangle> \<star>
               \<langle>ntt_layer_no_overflow l acs\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gr' cs'. r \<mapsto>\<langle>\<top>\<rangle> gr'\<down>cs' \<star>
               \<langle>refines_coeffs cs' (ntt_layer_int l acs)\<rangle>)
    in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_ntt_layer_contract(*>*)

lemma c_global_mlk_zetas_sint:
  assumes \<open>i < 128\<close>
   shows \<open>sint (c_global_mlk_zetas ! i) = zetas_int ! i\<close>
using assms by (simp add: c_global_mlk_zetas_def zetas_sword_unfold[symmetric] zetas_sword_sint)

(*<*)
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
(*>*)

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
              \<star> \<langle>k \<le> MLKEM_N\<rangle>\<close>
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
              \<star> \<langle>MLKEM_N - Suc k < 2^(unat layer_val - 1)\<rangle>\<close>
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
          c_global_mlk_zetas_def zetas_sword_unfold[symmetric]
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
    subgoal \<comment> \<open>Fuel exhaust\<close>
      by (crush_base simp add: min_absorb2 ntt_layer_nb_le_N ntt_layer_total_size_word)
    done
  subgoal \<comment> \<open>Shift amount bound\<close>
    by (simp add: unat_sub word_le_nat_alt)
  done

subsection \<open>@{text mlk_poly_ntt_c} contract\<close>

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
(*<*)ucincl_auto c_mlk_poly_ntt_c_contract(*>*)

text \<open>Lifted ntt\_layer contract: operates on the poly reference directly,
  avoiding the focused reference and its schematic resolution issues.\<close>

definition c_mlk_ntt_layer_poly_contract ::
  \<open>('addr, 8 word list, c_mlk_poly) Global_Store.ref \<Rightarrow> 8 word list \<Rightarrow>
   c_mlk_poly \<Rightarrow> int list \<Rightarrow> c_uint \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  [crush_contracts]: \<open>c_mlk_ntt_layer_poly_contract p gp vp acs layer_val \<equiv>
    let l    = unat layer_val;
        pre  = can_alloc_reference \<star>
               p \<mapsto>\<langle>\<top>\<rangle> gp\<down>vp \<star>
               \<langle>refines_coeffs (c_mlk_poly_coeffs vp) acs\<rangle> \<star>
               \<langle>1 \<le> l\<rangle> \<star>
               \<langle>l \<le> 7\<rangle> \<star>
               \<langle>ntt_layer_no_overflow l acs\<rangle>;
        post = \<lambda>_. can_alloc_reference \<star>
               (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
               \<langle>refines_coeffs cs' (ntt_layer_int l acs)\<rangle>)
    in make_function_contract pre post\<close>
(*<*)ucincl_auto c_mlk_ntt_layer_poly_contract(*>*)

text \<open>Lens validity and focused view/modify lemmas for @{type c_mlk_poly}.\<close>

lemma is_valid_lens_view_modify_c_mlk_poly:
  shows \<open>is_valid_lens_view_modify c_mlk_poly_coeffs update_c_mlk_poly_coeffs\<close>
  unfolding is_valid_lens_view_modify_def
proof (intro conjI allI impI)
   fix f s
  show \<open>c_mlk_poly_coeffs (update_c_mlk_poly_coeffs f s) = f (c_mlk_poly_coeffs s)\<close>
    by (cases s) (simp add: Datatype_Records.datatype_record_update(41) c_mlk_poly.simps)
next
     fix f s
  assume \<open>f (c_mlk_poly_coeffs s) = c_mlk_poly_coeffs s\<close>
  then show \<open>update_c_mlk_poly_coeffs f s = s\<close>
    by (cases s) (simp add: Datatype_Records.datatype_record_update(41) c_mlk_poly.simps)
next
   fix f g s
  show \<open>update_c_mlk_poly_coeffs f (update_c_mlk_poly_coeffs g s) =
        update_c_mlk_poly_coeffs (\<lambda>x. f (g x)) s\<close>
    by (cases s) (simp add: Datatype_Records.datatype_record_update(41) c_mlk_poly.simps)
qed

lemma focus_view_make_c_mlk_poly_eq:
  shows \<open>\<down>{Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify c_mlk_poly_coeffs
            update_c_mlk_poly_coeffs))} (make_c_mlk_poly cs) \<doteq> cs\<close>
  apply (subst lens_to_focus_raw_components'(1)[OF is_valid_lens_via_modifyI'[OF is_valid_lens_view_modify_c_mlk_poly]])
  apply (simp add: make_lens_via_view_modify_components c_mlk_poly.sel)
  done

lemma focus_view_make_c_mlk_poly [simp]:
  shows \<open>(\<down>{Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify c_mlk_poly_coeffs
            update_c_mlk_poly_coeffs))} v0 \<doteq> v1) \<longleftrightarrow> (v0 = make_c_mlk_poly v1)\<close>
using focus_view_make_c_mlk_poly_eq[of \<open>c_mlk_poly_coeffs v0\<close>] c_mlk_poly.collapse[of v0]
  by (auto simp add: c_mlk_poly.sel)

lemma focus_modify_make_c_mlk_poly [simp]:
  shows \<open>\<nabla>{Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify c_mlk_poly_coeffs update_c_mlk_poly_coeffs))}
            f (make_c_mlk_poly cs) = make_c_mlk_poly (f cs)\<close>
  apply (subst lens_to_focus_raw_components'(3)[OF is_valid_lens_via_modifyI'[OF is_valid_lens_view_modify_c_mlk_poly]])
  apply (subst make_lens_via_view_modify_components(3)[OF is_valid_lens_view_modify_c_mlk_poly])
  apply (simp add: Datatype_Records.datatype_record_update(41) c_mlk_poly.simps)
  done

lemma focusedL_c_mlk_poly:
  shows \<open>aentails_conditional_crule_strong
    (focus_reference (Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify c_mlk_poly_coeffs
            update_c_mlk_poly_coeffs))) r \<mapsto>\<langle>sh\<rangle> g1\<down>v1)
    (\<langle>g0 = g1\<rangle> \<star> \<langle>points_to_localizes r g0 (make_c_mlk_poly v1)\<rangle>)
    (\<langle>points_to_localizes (focus_reference (Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify c_mlk_poly_coeffs
            update_c_mlk_poly_coeffs))) r) g1 v1\<rangle>)
    (r \<mapsto>\<langle>sh\<rangle> g0\<down>(make_c_mlk_poly v1))\<close>
unfolding aentails_conditional_crule_strong_def by (crush_base simp add: points_to_def
    focus_view_make_c_mlk_poly_eq)

lemma focusedL_c_mlk_poly_aentails:
  shows \<open>focus_reference (Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify c_mlk_poly_coeffs
            update_c_mlk_poly_coeffs))) r \<mapsto>\<langle>sh\<rangle> g\<down>v \<longlongrightarrow> r \<mapsto>\<langle>sh\<rangle> g\<down>(make_c_mlk_poly v)\<close>
unfolding points_to_def
  apply (simp only: untype_ref_focus)
  apply (rule asepconj_mono)
  apply (simp add: apure_def aentails_def is_valid_ref_for_def focus_reference_def
    focus_focused_get_focus focus_compose_components bind_eq_Some_conv focus_view_make_c_mlk_poly)
  apply (clarsimp simp add: focus_dom.rep_eq focus_raw_dom_def focus_compose.rep_eq
    focus_raw_compose_def make_focus_raw_via_view_modify_def dom_def bind_eq_Some_conv
    focus_view.rep_eq[symmetric] focus_view_make_c_mlk_poly c_mlk_poly.collapse)
  apply (fastforce dest: subsetD intro: exI[where x="c_mlk_poly_coeffs _"])
  done

lemma focusedR_c_mlk_poly_aentails:
  shows \<open>r \<mapsto>\<langle>sh\<rangle> g\<down>v \<longlongrightarrow> focus_reference (Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify c_mlk_poly_coeffs
            update_c_mlk_poly_coeffs))) r \<mapsto>\<langle>sh\<rangle> g\<down>(c_mlk_poly_coeffs v)\<close>
unfolding points_to_def
  apply (simp only: untype_ref_focus)
  apply (rule asepconj_mono)
  apply (simp add: apure_def aentails_def is_valid_ref_for_def focus_reference_def
    focus_focused_get_focus focus_compose_components bind_eq_Some_conv focus_view_make_c_mlk_poly
    c_mlk_poly.sel c_mlk_poly.collapse)
  apply (clarsimp simp add: focus_dom.rep_eq focus_raw_dom_def focus_compose.rep_eq
    focus_raw_compose_def make_focus_raw_via_view_modify_def dom_def bind_eq_Some_conv
    focus_view.rep_eq[symmetric] focus_view_make_c_mlk_poly c_mlk_poly.collapse)
  apply fastforce
  done

lemma c_mlk_ntt_layer_poly_spec:
  shows \<open>\<Gamma>; c_mlk_ntt_layer MLKEM_N while_fuel while_fuel MLKEM_N
              (focus_reference (Abs_focus (\<integral>'\<^sub>l (make_lens_via_view_modify
                 c_mlk_poly_coeffs update_c_mlk_poly_coeffs))) p) layer_val \<Turnstile>\<^sub>F
            c_mlk_ntt_layer_poly_contract p gp vp acs layer_val\<close>
  apply (rule satisfies_function_contract_weaken[OF c_mlk_ntt_layer_spec[where
      gr=gp and cs=\<open>c_mlk_poly_coeffs vp\<close> and acs=acs]])
  apply (simp_all add: c_mlk_ntt_layer_poly_contract_def c_mlk_ntt_layer_contract_def Let_def)
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

lemma c_mlk_poly_ntt_c_spec [crush_specs]:
  notes focusedL_c_mlk_poly[crush_aentails_cond_crules, crush_points_to_cond_crules]
  shows \<open>\<Gamma>; c_mlk_poly_ntt_c MLKEM_N while_fuel while_fuel MLKEM_N 7 p \<Turnstile>\<^sub>F
            c_mlk_poly_ntt_c_contract p gp vp ap\<close>
  apply (crush_boot f: c_mlk_poly_ntt_c_def contract: c_mlk_poly_ntt_c_contract_def)
  apply crush_base
  subgoal for x
    apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>k. (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
              \<langle>length cs' = MLKEM_N\<rangle> \<star>
              \<langle>ntt_outer_loop_int (2 ^ (7 - k)) k (list.map sint cs') = poly_ntt_int ap\<rangle> \<star>
              \<langle>coeff_bound (int (8 - k) * MLKEM_Q) (list.map sint cs')\<rangle>)
              \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (8 - k) :: c_uint))
              \<star> can_alloc_reference\<close>
          and INV'=\<open>\<lambda>k. (\<Squnion>gp' cs'. p \<mapsto>\<langle>\<top>\<rangle> gp'\<down>(make_c_mlk_poly cs') \<star>
              \<langle>length cs' = MLKEM_N\<rangle> \<star>
              \<langle>ntt_outer_loop_int (2 ^ (6 - k)) (Suc k) (list.map sint cs') = poly_ntt_int ap\<rangle> \<star>
              \<langle>coeff_bound (int (7 - k) * MLKEM_Q) (list.map sint cs')\<rangle>)
              \<star> (\<Squnion>gx. x \<mapsto>\<langle>\<top>\<rangle> gx\<down>(of_nat (7 - k) :: c_uint))
              \<star> can_alloc_reference\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
    subgoal \<comment> \<open>Init + Finalization\<close>
      by (crush_base simp add: poly_ntt_int_def refines_mlk_poly_def
                               c_mlk_poly.collapse[symmetric] points_to_def)
    subgoal \<comment> \<open>Condition check\<close>
      by crush_base (simp_all add: word_le_nat_alt unat_of_nat unat_sub_if_size)
    subgoal for k \<comment> \<open>Loop body\<close>
      apply (crush_base no_schematics)
      apply (ucincl_discharge \<open>rule wp_callI[OF dereference_spec]\<close>)
      apply (force simp add: dereference_contract_def)
      apply (crush_base no_schematics simp add: dereference_contract_def)
      apply (ucincl_discharge \<open>rule wp_callI[OF c_mlk_ntt_layer_poly_spec]\<close>)
      apply (force simp add: c_mlk_ntt_layer_poly_contract_def Let_def c_mlk_poly.sel
          refines_coeffs_def)
      apply (crush_base no_schematics simp add: c_mlk_ntt_layer_poly_contract_def)
      apply (ucincl_discharge \<open>rule wp_callI[OF dereference_spec]\<close>)
      apply (force simp add: dereference_contract_def)
      apply (crush_base no_schematics simp add: dereference_contract_def word_le_nat_alt
          refines_coeffs_def)
      apply (ucincl_discharge \<open>rule wp_callI[OF update_spec]\<close>)
      apply (force simp add: update_contract_def)
      apply (crush_base no_schematics simp add: update_contract_def)
      apply (auto simp add: unat_of_nat word_less_nat_alt unat_sub_if_size word_size
          intro: coeff_bound_implies_ntt_layer_no_overflow[where l = \<open>7 - k\<close>])[3]
      subgoal for cs' cs'' cs''' cs'''' cs'''''
        apply (rule_tac x="\<nabla>{\<integral>\<^sub>p c_uint_prism} (\<lambda>_. 8 - word_of_nat k) cs'" in aentails_intro(7))
        apply (rule_tac x="cs''''" in aentails_intro(7))
        apply (rule_tac x="cs'''''" in aentails_intro(7))
        apply crush_base
        subgoal \<comment> \<open>coeff_bound\<close>
          apply (subgoal_tac \<open>unat (7 - word_of_nat k :: 32 word) = 7 - k\<close>)
          prefer 2 apply (simp add: unat_of_nat word_less_nat_alt unat_sub_if_size word_size)
          apply (simp only:)
          apply (subgoal_tac \<open>coeff_bound (int ((7-k)+1) * MLKEM_Q) (ntt_layer_int (7-k) (list.map sint cs'''))\<close>)
          apply (simp add: of_nat_diff algebra_simps)
          apply (rule ntt_layer_int_bound[where l=\<open>7 - k\<close>])
          apply (auto simp add: of_nat_diff algebra_simps)
          done
        subgoal \<comment> \<open>ntt_outer_loop\<close>
          apply (subgoal_tac \<open>unat (7 - word_of_nat k :: 32 word) = 7 - k\<close>)
          prefer 2 apply (simp add: unat_of_nat word_less_nat_alt unat_sub_if_size word_size)
          apply (simp only:)
          apply (simp only: ntt_layer_int_def)
          apply (simp only: ntt_middle_loop_int_fst case_prod_beta)
          apply (subgoal_tac \<open>(2::nat) ^ (7 - k) = 2 ^ (6 - k) + 2 ^ (6 - k)\<close>)
          apply simp
          apply (subgoal_tac \<open>(7::nat) - k = Suc (6 - k)\<close>)
          apply simp
          apply simp
          done
        done
      done
    subgoal \<comment> \<open>Fuel exhaust\<close>
      by crush_base
  done
done

subsection \<open>@{text mlk_poly_ntt} contract\<close>

text \<open>Top-level wrapper: delegates to @{verbatim \<open>mlk_poly_ntt_c\<close>} via
  the @{const refines_mlk_poly} abstraction boundary.\<close>

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
(*<*)ucincl_auto c_mlk_poly_ntt_contract(*>*)

lemma c_mlk_poly_ntt_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_ntt 7 MLKEM_N while_fuel while_fuel MLKEM_N p \<Turnstile>\<^sub>F
            c_mlk_poly_ntt_contract p gp vp ap\<close>
  apply (crush_boot f: c_mlk_poly_ntt_def contract: c_mlk_poly_ntt_contract_def)
  apply (rule wp_callI[OF c_mlk_poly_ntt_c_spec[where gp=gp and vp=vp and ap=ap]])
  apply (simp add: c_mlk_poly_ntt_c_contract_def)
  apply (crush_base simp add: c_mlk_poly_ntt_c_contract_def)
  done

(*<*)
end
(*>*)

(*<*)
end
(*>*)
