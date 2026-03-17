(*<*)
theory MLKEM_NTT_Correctness
  imports MLKEM_InvNTT_Spec
begin
(*>*)

section \<open>NTT / Inverse-NTT Inverse Relationship\<close>

text \<open>
  The forward NTT and inverse NTT with Montgomery prescaling are two-sided
  inverses modulo @{const MLKEM_Q}, up to a multiplicative factor of
  @{text "2^16"} (the Montgomery radix R).  The proof is structured in
  tiers, from low-level infrastructure through butterfly, loop, layer,
  and linearity lemmas, culminating in the full-transform composition
  theorems @{text poly_ntt_invntt_tomont} and @{text poly_invntt_tomont_ntt}.
\<close>

text_raw \<open>
\begin{figure}[ht]
\centering
\begin{tikzpicture}[>=Stealth,
    tier/.style={draw=mlkblue, fill=mlklightblue, rounded corners,
                 minimum width=3.8cm, minimum height=0.7cm,
                 align=center, font=\small},
    node distance=0.6cm]
  \node[tier] (t0) {Tier 0: Infrastructure};
  \node[tier, below=of t0] (t1) {Tier 1: Zeta Properties};
  \node[tier, below=of t1] (t2) {Tier 2: Bound Propagation};
  \node[tier, below=of t2] (t3) {Tier 3: Butterfly Composition};
  \node[tier, below=of t3] (t4) {Tier 4: Loop Composition};
  \node[tier, below=of t4] (t5) {Tier 5: Layer Inverse};
  \node[tier, below=of t5] (t6) {Tier 6: Linearity};
  \node[tier, below=of t6] (t7) {Tier 7: Full Composition};
  \draw[->,thick,mlkblue] (t0) -- (t1);
  \draw[->,thick,mlkblue] (t1) -- (t2);
  \draw[->,thick,mlkblue] (t2) -- (t3);
  \draw[->,thick,mlkblue] (t3) -- (t4);
  \draw[->,thick,mlkblue] (t4) -- (t5);
  \draw[->,thick,mlkblue] (t5) -- (t6);
  \draw[->,thick,mlkblue] (t6) -- (t7);
\end{tikzpicture}
\caption{Proof tier hierarchy.  Each tier builds on results from the tier
  above; the final composition theorems at Tier~7 connect the forward and
  inverse NTT as two-sided inverses modulo~$q$.}
\label{fig:proof-tiers}
\end{figure}
\<close>

subsection \<open>Tier 0 — Infrastructure\<close>

(*<*)
lemma centered_mod_mod:
  assumes \<open>q > 0\<close>
    shows \<open>centered_mod x q mod q = x mod q\<close>
unfolding centered_mod_def Let_def by (simp add: mod_diff_right_eq)

lemma fqmul_int_cong:
  shows \<open>fqmul_int a b * 2^16 mod MLKEM_Q = a * b mod MLKEM_Q\<close>
unfolding fqmul_int_def by (rule montgomery_reduce_int_correct)
(*>*)

subsection \<open>Tier 1 — Zeta Properties\<close>

(*<*)

lemma zetas_int_mod:
  assumes \<open>i < 128\<close>
    shows \<open>zetas_int ! i mod MLKEM_Q = mlkem_zeta ^ bit_reverse 7 i * 2^16 mod MLKEM_Q\<close>
using assms by (simp add: zetas_int_roots_of_unity centered_mod_mod)

text \<open>The product of conjugate zeta powers equals @{text "-1 mod Q"}, i.e.
  @{text "\<zeta>^{br(k)} \<sqdot> \<zeta>^{br(k')} \<equiv> -1 (mod Q)"} when bit-reversed indices
  sum to 128.\<close>

lemma zeta_power_sum_128:
  assumes \<open>a + b = 128\<close>
    shows \<open>mlkem_zeta ^ a * mlkem_zeta ^ b mod MLKEM_Q = MLKEM_Q - 1\<close>
proof -
  have \<open>mlkem_zeta ^ a * mlkem_zeta ^ b = mlkem_zeta ^ (a + b)\<close>
    by (simp add: power_add)
  thus ?thesis
    using assms mlkem_zeta_half_order by simp
qed

lemma bit_reverse_bound:
  assumes \<open>k < 2^n\<close>
    shows \<open>bit_reverse n k < 2^n\<close>
using assms proof (induction n arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have \<open>k div 2 < 2^n\<close>
    using Suc.prems by simp
  hence IH: \<open>bit_reverse n (k div 2) < 2^n\<close>
    by (rule Suc.IH)
  have \<open>k mod 2 * 2^n + bit_reverse n (k div 2) < 2 * 2^n\<close>
  proof -
    have \<open>k mod 2 \<le> 1\<close>
      by simp
    hence \<open>k mod 2 * 2^n \<le> 2^n\<close>
      by (simp add: mult_le_cancel2)
    thus ?thesis
      using IH by linarith
  qed
  thus ?case
    by simp
qed

text \<open>Bit-reverse complement: for indices in the NTT butterfly pattern,
  the bit-reversed forward and inverse zeta indices sum to 128.\<close>

lemma bit_reverse_complement:
  assumes \<open>j < 2^(l-1)\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
    shows \<open>bit_reverse 7 (2^(l-1) + j) + bit_reverse 7 (2^l - 1 - j) = 128\<close>
proof -
  have \<open>list_all (\<lambda>l. list_all
          (\<lambda>j. bit_reverse 7 (2^(l-1) + j) + bit_reverse 7 (2^l - 1 - j) = 128)
          [0..<2^(l-1)]) [1..<8::nat]\<close>
    by eval
  thus ?thesis
    using assms by (auto simp: list_all_iff)
qed
(*>*)

subsection \<open>Tier 2 — Butterfly Values and Montgomery Cancellation\<close>

text \<open>Montgomery-radix inverse: @{text "2^16 \<sqdot> 169 \<equiv> 1 (mod Q)"}.\<close>

lemma R_inv_mod_Q:
  shows \<open>(2::int)^16 * 169 mod MLKEM_Q = 1\<close>
by eval

text \<open>Key cancellation: when a zeta argument carries a Montgomery factor
  @{text "2^16"}, it cancels with the @{text "R^{-1}"} inside @{const fqmul_int}.\<close>

lemma fqmul_zeta_cancel:
  assumes \<open>zeta mod MLKEM_Q = z_math * 2^16 mod MLKEM_Q\<close>
    shows \<open>fqmul_int a zeta mod MLKEM_Q = a * z_math mod MLKEM_Q\<close>
proof -
  have eq: \<open>fqmul_int a zeta * 2^16 mod MLKEM_Q = a * z_math * 2^16 mod MLKEM_Q\<close>
  proof -
    have \<open>fqmul_int a zeta * 2^16 mod MLKEM_Q = a * zeta mod MLKEM_Q\<close>
      by (rule fqmul_int_cong)
    also have \<open>a * zeta mod MLKEM_Q = a * (zeta mod MLKEM_Q) mod MLKEM_Q\<close>
      by (rule mod_mult_right_eq[symmetric])
    also have \<open>\<dots> = a * (z_math * 2^16 mod MLKEM_Q) mod MLKEM_Q\<close>
      using assms by simp
    also have \<open>\<dots> = a * (z_math * 2^16) mod MLKEM_Q\<close>
      by (rule mod_mult_right_eq)
    also have \<open>\<dots> = a * z_math * 2^16 mod MLKEM_Q\<close>
      by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  from eq show ?thesis
  proof -
    have lhs: \<open>fqmul_int a zeta mod MLKEM_Q = (fqmul_int a zeta * 2^16) * 169 mod MLKEM_Q\<close>
    proof -
      have \<open>fqmul_int a zeta mod MLKEM_Q = fqmul_int a zeta * 1 mod MLKEM_Q\<close>
        by simp
      also have \<open>\<dots> = fqmul_int a zeta * (2^16 * 169 mod MLKEM_Q) mod MLKEM_Q\<close>
        using R_inv_mod_Q by simp
      also have \<open>\<dots> = fqmul_int a zeta * (2^16 * 169) mod MLKEM_Q\<close>
        by (rule mod_mult_right_eq)
      finally show ?thesis
        by (simp add: mult.assoc)
    qed
    have rhs: \<open>a * z_math mod MLKEM_Q = (a * z_math * 2^16) * 169 mod MLKEM_Q\<close>
    proof -
      have \<open>a * z_math mod MLKEM_Q = a * z_math * 1 mod MLKEM_Q\<close>
        by simp
      also have \<open>\<dots> = a * z_math * (2^16 * 169 mod MLKEM_Q) mod MLKEM_Q\<close>
        using R_inv_mod_Q by simp
      also have \<open>\<dots> = a * z_math * (2^16 * 169) mod MLKEM_Q\<close>
        by (rule mod_mult_right_eq)
      finally show ?thesis
        by (simp add: mult.assoc)
    qed
    have mid: \<open>(fqmul_int a zeta * 2^16) * 169 mod MLKEM_Q = (a * z_math * 2^16) * 169 mod MLKEM_Q\<close>
    proof -
      have \<open>(fqmul_int a zeta * 2^16) * 169 mod MLKEM_Q =
            (fqmul_int a zeta * 2^16 mod MLKEM_Q) * 169 mod MLKEM_Q\<close>
        by (rule mod_mult_left_eq[symmetric])
      also have \<open>\<dots> = (a * z_math * 2^16 mod MLKEM_Q) * 169 mod MLKEM_Q\<close>
        using eq by simp
      also have \<open>\<dots> = (a * z_math * 2^16) * 169 mod MLKEM_Q\<close>
        by (rule mod_mult_left_eq)
      finally show ?thesis .
    qed
    show ?thesis
      using lhs mid rhs by simp
  qed
qed

text \<open>Butterfly exact values — unfolding the list-update structure.\<close>

lemma ntt_butterfly_int_val_low:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
    shows \<open>ntt_butterfly_int zeta j blen cs ! j =
             cs ! j + fqmul_int (cs ! (j + blen)) zeta\<close>
unfolding ntt_butterfly_int_def Let_def using assms by simp

lemma ntt_butterfly_int_val_high:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
    shows \<open>ntt_butterfly_int zeta j blen cs ! (j + blen) =
             cs ! j - fqmul_int (cs ! (j + blen)) zeta\<close>
unfolding ntt_butterfly_int_def Let_def using assms by auto

lemma invntt_butterfly_int_val_low:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
    shows \<open>invntt_butterfly_int zeta j blen cs ! j =
             barrett_reduce_int (cs ! j + cs ! (j + blen))\<close>
unfolding invntt_butterfly_int_def Let_def using assms by auto

lemma invntt_butterfly_int_val_high:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
    shows \<open>invntt_butterfly_int zeta j blen cs ! (j + blen) =
             fqmul_int (cs ! (j + blen) - cs ! j) zeta\<close>
unfolding invntt_butterfly_int_def Let_def using assms by simp

text \<open>Mod-Q butterfly characterization (combining exact values with
  @{thm fqmul_zeta_cancel} and @{thm barrett_reduce_mod}).\<close>

lemma ntt_butterfly_int_mod_low:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
      and \<open>zeta mod MLKEM_Q = z_math * 2^16 mod MLKEM_Q\<close>
    shows \<open>ntt_butterfly_int zeta j blen cs ! j mod MLKEM_Q =
             (cs ! j + cs ! (j + blen) * z_math) mod MLKEM_Q\<close>
using ntt_butterfly_int_val_low[OF assms(1,2)]
  fqmul_zeta_cancel[OF assms(3), of \<open>cs ! (j + blen)\<close>]
proof -
  assume val: \<open>\<And>zeta. ntt_butterfly_int zeta j blen cs ! j = cs ! j + fqmul_int (cs ! (j + blen)) zeta\<close>
  assume cancel: \<open>fqmul_int (cs ! (j + blen)) zeta mod MLKEM_Q = cs ! (j + blen) * z_math mod MLKEM_Q\<close>
  have \<open>ntt_butterfly_int zeta j blen cs ! j mod MLKEM_Q =
        (cs ! j + fqmul_int (cs ! (j + blen)) zeta) mod MLKEM_Q\<close>
    using val by simp
  also have \<open>\<dots> = (cs ! j + fqmul_int (cs ! (j + blen)) zeta mod MLKEM_Q) mod MLKEM_Q\<close>
    by (rule mod_add_right_eq[symmetric])
  also have \<open>\<dots> = (cs ! j + cs ! (j + blen) * z_math mod MLKEM_Q) mod MLKEM_Q\<close>
    using cancel by simp
  also have \<open>\<dots> = (cs ! j + cs ! (j + blen) * z_math) mod MLKEM_Q\<close>
    by (rule mod_add_right_eq)
  finally show ?thesis .
qed

lemma ntt_butterfly_int_mod_high:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
      and \<open>zeta mod MLKEM_Q = z_math * 2^16 mod MLKEM_Q\<close>
    shows \<open>ntt_butterfly_int zeta j blen cs ! (j + blen) mod MLKEM_Q =
             (cs ! j - cs ! (j + blen) * z_math) mod MLKEM_Q\<close>
using ntt_butterfly_int_val_high[OF assms(1,2)]
  fqmul_zeta_cancel[OF assms(3), of \<open>cs ! (j + blen)\<close>]
proof -
  assume val: \<open>\<And>zeta. ntt_butterfly_int zeta j blen cs ! (j + blen) = cs ! j - fqmul_int (cs ! (j + blen)) zeta\<close>
  assume cancel: \<open>fqmul_int (cs ! (j + blen)) zeta mod MLKEM_Q = cs ! (j + blen) * z_math mod MLKEM_Q\<close>
  have \<open>ntt_butterfly_int zeta j blen cs ! (j + blen) mod MLKEM_Q =
        (cs ! j - fqmul_int (cs ! (j + blen)) zeta) mod MLKEM_Q\<close>
    using val by simp
  also have \<open>\<dots> = (cs ! j - fqmul_int (cs ! (j + blen)) zeta mod MLKEM_Q) mod MLKEM_Q\<close>
    by (rule mod_diff_right_eq[symmetric])
  also have \<open>\<dots> = (cs ! j - cs ! (j + blen) * z_math mod MLKEM_Q) mod MLKEM_Q\<close>
    using cancel by simp
  also have \<open>\<dots> = (cs ! j - cs ! (j + blen) * z_math) mod MLKEM_Q\<close>
    by (rule mod_diff_right_eq)
  finally show ?thesis .
qed

lemma invntt_butterfly_int_mod_low:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
    shows \<open>invntt_butterfly_int zeta j blen cs ! j mod MLKEM_Q =
             (cs ! j + cs ! (j + blen)) mod MLKEM_Q\<close>
using invntt_butterfly_int_val_low[OF assms] barrett_reduce_mod by simp

lemma invntt_butterfly_int_mod_high:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
      and \<open>zeta mod MLKEM_Q = z_math * 2^16 mod MLKEM_Q\<close>
    shows \<open>invntt_butterfly_int zeta j blen cs ! (j + blen) mod MLKEM_Q =
             (cs ! (j + blen) - cs ! j) * z_math mod MLKEM_Q\<close>
using invntt_butterfly_int_val_high[OF assms(1,2)]
  fqmul_zeta_cancel[OF assms(3), of \<open>cs ! (j + blen) - cs ! j\<close>] by simp

subsection \<open>Tier 3 — Butterfly Composition\<close>

text \<open>Composing inverse-then-forward (or forward-then-inverse) butterflies
  with conjugate zetas doubles each coefficient mod Q.\<close>

lemma butterfly_inverse_composition:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
      and \<open>mlkem_zeta ^ br_fwd * mlkem_zeta ^ br_inv mod MLKEM_Q = MLKEM_Q - 1\<close>
      and \<open>zf mod MLKEM_Q = mlkem_zeta ^ br_fwd * 2^16 mod MLKEM_Q\<close>
      and \<open>zi mod MLKEM_Q = mlkem_zeta ^ br_inv * 2^16 mod MLKEM_Q\<close>
    shows \<open>ntt_butterfly_int zf j blen (invntt_butterfly_int zi j blen cs) ! j mod MLKEM_Q =
              2 * cs ! j mod MLKEM_Q\<close>
      and \<open>ntt_butterfly_int zf j blen (invntt_butterfly_int zi j blen cs) ! (j + blen) mod MLKEM_Q =
              2 * cs ! (j + blen) mod MLKEM_Q\<close>
proof -
  define cs' where
    \<open>cs' = invntt_butterfly_int zi j blen cs\<close>
  let ?D = \<open>cs ! (j + blen) - cs ! j\<close>
  let ?Zf = \<open>mlkem_zeta ^ br_fwd\<close>
  let ?Zi = \<open>mlkem_zeta ^ br_inv\<close>
  have jb: \<open>j + blen < length cs'\<close>
    using assms(1) unfolding cs'_def by (simp add: invntt_butterfly_int_length)
  have cs'_j_mod: \<open>cs' ! j mod MLKEM_Q = (cs ! j + cs ! (j + blen)) mod MLKEM_Q\<close>
    unfolding cs'_def using invntt_butterfly_int_mod_low[OF assms(1,2)] by simp
  have cs'_jb_mod: \<open>cs' ! (j + blen) mod MLKEM_Q = ?D * ?Zi mod MLKEM_Q\<close>
    unfolding cs'_def using invntt_butterfly_int_mod_high[OF assms(1,2,5)] by simp
  have product_mod: \<open>(cs' ! (j + blen) * ?Zf) mod MLKEM_Q = (?D * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
  proof -
    have \<open>(cs' ! (j + blen) * ?Zf) mod MLKEM_Q =
          (cs' ! (j + blen) mod MLKEM_Q * ?Zf) mod MLKEM_Q\<close>
      by (rule mod_mult_left_eq[symmetric])
    also have \<open>\<dots> = (?D * ?Zi mod MLKEM_Q * ?Zf) mod MLKEM_Q\<close>
      using cs'_jb_mod by simp
    also have \<open>\<dots> = (?D * ?Zi * ?Zf) mod MLKEM_Q\<close>
      by (rule mod_mult_left_eq)
    also have \<open>\<dots> = (?D * (?Zi * ?Zf)) mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = (?D * (?Zi * ?Zf mod MLKEM_Q)) mod MLKEM_Q\<close>
      by (rule mod_mult_right_eq[symmetric])
    also have \<open>\<dots> = (?D * (?Zf * ?Zi mod MLKEM_Q)) mod MLKEM_Q\<close>
      by (simp add: mult.commute[of ?Zi ?Zf])
    also have \<open>\<dots> = (?D * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
      using assms(3) by simp
    finally show ?thesis .
  qed
  show \<open>ntt_butterfly_int zf j blen (invntt_butterfly_int zi j blen cs) ! j mod MLKEM_Q =
            2 * cs ! j mod MLKEM_Q\<close>
  proof -
    have \<open>ntt_butterfly_int zf j blen cs' ! j mod MLKEM_Q =
          (cs' ! j + cs' ! (j + blen) * ?Zf) mod MLKEM_Q\<close>
      using ntt_butterfly_int_mod_low[OF jb assms(2,4)] by simp
    also have \<open>\<dots> = ((cs ! j + cs ! (j + blen)) + ?D * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
      by (rule mod_add_cong[OF cs'_j_mod product_mod])
    also have \<open>\<dots> = 2 * cs ! j mod MLKEM_Q\<close>
      by (simp add: mod_eq_dvd_iff algebra_simps)
    finally show ?thesis
      unfolding cs'_def .
  qed
  show \<open>ntt_butterfly_int zf j blen (invntt_butterfly_int zi j blen cs) ! (j + blen) mod MLKEM_Q =
            2 * cs ! (j + blen) mod MLKEM_Q\<close>
  proof -
    have \<open>ntt_butterfly_int zf j blen cs' ! (j + blen) mod MLKEM_Q =
          (cs' ! j - cs' ! (j + blen) * ?Zf) mod MLKEM_Q\<close>
      using ntt_butterfly_int_mod_high[OF jb assms(2,4)] by simp
    also have \<open>\<dots> = ((cs ! j + cs ! (j + blen)) - ?D * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
      by (rule mod_diff_cong[OF cs'_j_mod product_mod])
    also have \<open>\<dots> = 2 * cs ! (j + blen) mod MLKEM_Q\<close>
      by (simp add: mod_eq_dvd_iff algebra_simps)
    finally show ?thesis
      unfolding cs'_def .
  qed
qed

lemma butterfly_forward_composition:
  assumes \<open>j + blen < length cs\<close>
      and \<open>blen > 0\<close>
      and \<open>mlkem_zeta ^ br_fwd * mlkem_zeta ^ br_inv mod MLKEM_Q = MLKEM_Q - 1\<close>
      and \<open>zf mod MLKEM_Q = mlkem_zeta ^ br_fwd * 2^16 mod MLKEM_Q\<close>
      and \<open>zi mod MLKEM_Q = mlkem_zeta ^ br_inv * 2^16 mod MLKEM_Q\<close>
    shows \<open>invntt_butterfly_int zi j blen (ntt_butterfly_int zf j blen cs) ! j mod MLKEM_Q =
             2 * cs ! j mod MLKEM_Q\<close>
      and \<open>invntt_butterfly_int zi j blen (ntt_butterfly_int zf j blen cs) ! (j + blen) mod MLKEM_Q =
             2 * cs ! (j + blen) mod MLKEM_Q\<close>
proof -
  define cs' where
    \<open>cs' = ntt_butterfly_int zf j blen cs\<close>
  have jb: \<open>j + blen < length cs'\<close>
    using assms(1) unfolding cs'_def by (simp add: ntt_butterfly_int_length)
  have val_low: \<open>cs' ! j = cs ! j + fqmul_int (cs ! (j + blen)) zf\<close>
    unfolding cs'_def using ntt_butterfly_int_val_low[OF assms(1,2)] by simp
  have val_high: \<open>cs' ! (j + blen) = cs ! j - fqmul_int (cs ! (j + blen)) zf\<close>
    unfolding cs'_def using ntt_butterfly_int_val_high[OF assms(1,2)] by simp
  have sum_eq: \<open>cs' ! j + cs' ! (j + blen) = 2 * cs ! j\<close>
    using val_low val_high by simp
  have diff_eq: \<open>cs' ! (j + blen) - cs' ! j = (-2) * fqmul_int (cs ! (j + blen)) zf\<close>
    using val_low val_high by simp
  have fqmul_cancel: \<open>fqmul_int (cs ! (j + blen)) zf mod MLKEM_Q =
        cs ! (j + blen) * (mlkem_zeta ^ br_fwd) mod MLKEM_Q\<close>
    using fqmul_zeta_cancel[OF assms(4), of \<open>cs ! (j + blen)\<close>] .
  have neg2_Q_mod: \<open>(-2) * (x::int) * (MLKEM_Q - 1) mod MLKEM_Q = 2 * x mod MLKEM_Q\<close> for x
    by (simp add: mod_eq_dvd_iff algebra_simps)
  show \<open>invntt_butterfly_int zi j blen (ntt_butterfly_int zf j blen cs) ! j mod MLKEM_Q =
         2 * cs ! j mod MLKEM_Q\<close>
  proof -
    have \<open>invntt_butterfly_int zi j blen cs' ! j mod MLKEM_Q =
          (cs' ! j + cs' ! (j + blen)) mod MLKEM_Q\<close>
      using invntt_butterfly_int_mod_low[OF jb assms(2)] by simp
    also have \<open>\<dots> = 2 * cs ! j mod MLKEM_Q\<close>
      using sum_eq by simp
    finally show ?thesis
      unfolding cs'_def .
  qed
  show \<open>invntt_butterfly_int zi j blen (ntt_butterfly_int zf j blen cs) ! (j + blen) mod MLKEM_Q =
         2 * cs ! (j + blen) mod MLKEM_Q\<close>
  proof -
    let ?X = \<open>cs ! (j + blen)\<close>
    let ?Zf = \<open>mlkem_zeta ^ br_fwd\<close>
    let ?Zi = \<open>mlkem_zeta ^ br_inv\<close>
    have \<open>invntt_butterfly_int zi j blen cs' ! (j + blen) mod MLKEM_Q =
          (cs' ! (j + blen) - cs' ! j) * ?Zi mod MLKEM_Q\<close>
      using invntt_butterfly_int_mod_high[OF jb assms(2,5)] by simp
    also have \<open>\<dots> = (-2) * fqmul_int ?X zf * ?Zi mod MLKEM_Q\<close>
      using diff_eq by simp
    also have \<open>\<dots> = (-2) * (?X * ?Zf) * ?Zi mod MLKEM_Q\<close>
    proof -
      have \<open>(-2) * fqmul_int ?X zf * ?Zi mod MLKEM_Q =
            (((-2) * fqmul_int ?X zf mod MLKEM_Q) * ?Zi) mod MLKEM_Q\<close>
        by (rule mod_mult_left_eq[symmetric])
      also have \<open>(-2) * fqmul_int ?X zf mod MLKEM_Q = (-2) * (?X * ?Zf) mod MLKEM_Q\<close>
      proof -
        have \<open>(-2) * fqmul_int ?X zf mod MLKEM_Q =
              ((-2) * (fqmul_int ?X zf mod MLKEM_Q)) mod MLKEM_Q\<close>
          by (rule mod_mult_right_eq[symmetric])
        also have \<open>\<dots> = ((-2) * (?X * ?Zf mod MLKEM_Q)) mod MLKEM_Q\<close>
          using fqmul_cancel by simp
        also have \<open>\<dots> = (-2) * (?X * ?Zf) mod MLKEM_Q\<close>
          by (rule mod_mult_right_eq)
        finally show ?thesis .
      qed
      hence \<open>(((-2) * fqmul_int ?X zf mod MLKEM_Q) * ?Zi) mod MLKEM_Q =
             (((-2) * (?X * ?Zf) mod MLKEM_Q) * ?Zi) mod MLKEM_Q\<close>
        by simp
      also have \<open>\<dots> = ((-2) * (?X * ?Zf) * ?Zi) mod MLKEM_Q\<close>
        by (rule mod_mult_left_eq)
      finally show ?thesis
        by simp
    qed
    also have \<open>\<dots> = (-2) * ?X * (?Zf * ?Zi) mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = (-2) * ?X * (MLKEM_Q - 1) mod MLKEM_Q\<close>
    proof -
      have \<open>(-2) * ?X * (?Zf * ?Zi) mod MLKEM_Q =
            ((-2) * ?X * (?Zf * ?Zi mod MLKEM_Q)) mod MLKEM_Q\<close>
        by (rule mod_mult_right_eq[symmetric])
      also have \<open>\<dots> = ((-2) * ?X * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
        using assms(3) by simp
      finally show ?thesis .
    qed
    also have \<open>\<dots> = 2 * ?X mod MLKEM_Q\<close>
      by (rule neg2_Q_mod)
    finally show ?thesis
      unfolding cs'_def .
  qed
qed

subsection \<open>Tier 4 — Loop Composition\<close>

text \<open>Composing forward and inverse inner/middle loops with matching zeta
  pairs yields pointwise scaling by 2 mod Q.\<close>

text \<open>Helper: composing two @{const fqmul_int} with conjugate zetas cancels
  Montgomery factors and yields multiplication by @{text "Q - 1 mod Q"}.\<close>

lemma fqmul_fqmul_cancel:
  assumes \<open>zf mod MLKEM_Q = mlkem_zeta ^ br_fwd * 2^16 mod MLKEM_Q\<close>
      and \<open>zi mod MLKEM_Q = mlkem_zeta ^ br_inv * 2^16 mod MLKEM_Q\<close>
      and \<open>mlkem_zeta ^ br_fwd * mlkem_zeta ^ br_inv mod MLKEM_Q = MLKEM_Q - 1\<close>
    shows \<open>fqmul_int (fqmul_int a zi) zf mod MLKEM_Q =
             a * (MLKEM_Q - 1) mod MLKEM_Q\<close>
proof -
  let ?Zf = \<open>mlkem_zeta ^ br_fwd\<close>
  let ?Zi = \<open>mlkem_zeta ^ br_inv\<close>
  have \<open>fqmul_int (fqmul_int a zi) zf mod MLKEM_Q =
        fqmul_int a zi * ?Zf mod MLKEM_Q\<close>
    by (rule fqmul_zeta_cancel[OF assms(1)])
  also have \<open>\<dots> = (fqmul_int a zi mod MLKEM_Q * ?Zf) mod MLKEM_Q\<close>
    by (rule mod_mult_left_eq[symmetric])
  also have \<open>\<dots> = (a * ?Zi mod MLKEM_Q * ?Zf) mod MLKEM_Q\<close>
    using fqmul_zeta_cancel[OF assms(2)] by simp
  also have \<open>\<dots> = (a * ?Zi * ?Zf) mod MLKEM_Q\<close>
    by (rule mod_mult_left_eq)
  also have \<open>\<dots> = (a * (?Zf * ?Zi)) mod MLKEM_Q\<close>
    by (simp add: algebra_simps)
  also have \<open>\<dots> = (a * (?Zf * ?Zi mod MLKEM_Q)) mod MLKEM_Q\<close>
    by (rule mod_mult_right_eq[symmetric])
  also have \<open>\<dots> = a * (MLKEM_Q - 1) mod MLKEM_Q\<close>
    using assms(3) by simp
  finally show ?thesis .
qed

lemma inner_loop_composition_invntt_ntt:
  assumes \<open>length cs = MLKEM_N\<close>
      and \<open>off + 2 * blen \<le> MLKEM_N\<close>
      and \<open>cnt \<le> blen\<close>
      and \<open>mlkem_zeta ^ br_fwd * mlkem_zeta ^ br_inv mod MLKEM_Q = MLKEM_Q - 1\<close>
      and \<open>zf mod MLKEM_Q = mlkem_zeta ^ br_fwd * 2^16 mod MLKEM_Q\<close>
      and \<open>zi mod MLKEM_Q = mlkem_zeta ^ br_inv * 2^16 mod MLKEM_Q\<close>
      and \<open>i < length cs\<close>
    shows \<open>ntt_inner_loop_int zf off blen cnt (invntt_inner_loop_int zi off blen cnt cs) ! i mod MLKEM_Q =
             (if i \<in> {off..<off+cnt} \<or> i \<in> {off+blen..<off+cnt+blen} then
                2 * cs ! i mod MLKEM_Q
              else
                cs ! i mod MLKEM_Q)\<close>
proof -
  define inv_cs where
    \<open>inv_cs = invntt_inner_loop_int zi off blen cnt cs\<close>
  have len_inv: \<open>length inv_cs = length cs\<close>
    by (simp add: inv_cs_def invntt_inner_loop_int_length)
  have off_bound: \<open>off + 2 * blen \<le> length cs\<close>
    using assms(1,2) by simp
  have case_low: \<open>i \<in> {off..<off+cnt} \<Longrightarrow> ?thesis\<close>
  proof -
    assume low: \<open>i \<in> {off..<off+cnt}\<close>
    define m where
      \<open>m = i - off\<close>
    have im1: \<open>i = off + m\<close> and im2: \<open>m < cnt\<close>
      using low by (auto simp: m_def)
    let ?a = \<open>cs ! (off + m)\<close>
    let ?b = \<open>cs ! (off + m + blen)\<close>
    let ?D = \<open>?b - ?a\<close>
    have ntt_val: \<open>ntt_inner_loop_int zf off blen cnt inv_cs ! (off + m) =
          inv_cs ! (off + m) + fqmul_int (inv_cs ! (off + m + blen)) zf\<close>
      by (rule ntt_inner_loop_int_low_val[OF im2 assms(3)])
         (use len_inv off_bound in simp)
    have inv_low: \<open>inv_cs ! (off + m) = barrett_reduce_int (?a + ?b)\<close>
      unfolding inv_cs_def by (rule invntt_inner_loop_int_low_val[OF im2 assms(3) off_bound])
    have inv_high: \<open>inv_cs ! (off + m + blen) = fqmul_int ?D zi\<close>
      unfolding inv_cs_def by (rule invntt_inner_loop_int_high_val[OF im2 assms(3) off_bound])
    have \<open>ntt_inner_loop_int zf off blen cnt inv_cs ! (off + m) mod MLKEM_Q =
            (barrett_reduce_int (?a + ?b) + fqmul_int (fqmul_int ?D zi) zf) mod MLKEM_Q\<close>
      using ntt_val inv_low inv_high by simp
    also have \<open>\<dots> = ((?a + ?b) + ?D * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
      by (rule mod_add_cong[OF barrett_reduce_mod fqmul_fqmul_cancel[OF assms(5,6,4)]])
    also have \<open>\<dots> = 2 * ?a mod MLKEM_Q\<close>
      by (simp add: mod_eq_dvd_iff algebra_simps)
    finally show ?thesis
      using im1 im2 low by (simp add: inv_cs_def)
  qed
  have case_high: \<open>i \<in> {off+blen..<off+cnt+blen} \<Longrightarrow> i \<notin> {off..<off+cnt} \<Longrightarrow> ?thesis\<close>
  proof -
    assume high: \<open>i \<in> {off+blen..<off+cnt+blen}\<close>
       and not_low: \<open>i \<notin> {off..<off+cnt}\<close>
    define m where
      \<open>m = i - off - blen\<close>
    have im1: \<open>i = off + m + blen\<close> and im2: \<open>m < cnt\<close>
      using high assms(3) by (auto simp: m_def)
    let ?a = \<open>cs ! (off + m)\<close>
    let ?b = \<open>cs ! (off + m + blen)\<close>
    let ?D = \<open>?b - ?a\<close>
    have ntt_val: \<open>ntt_inner_loop_int zf off blen cnt inv_cs ! (off + m + blen) =
          inv_cs ! (off + m) - fqmul_int (inv_cs ! (off + m + blen)) zf\<close>
      by (rule ntt_inner_loop_int_high_val[OF im2 assms(3)])
         (use len_inv off_bound in simp)
    have inv_low: \<open>inv_cs ! (off + m) = barrett_reduce_int (?a + ?b)\<close>
      unfolding inv_cs_def by (rule invntt_inner_loop_int_low_val[OF im2 assms(3) off_bound])
    have inv_high: \<open>inv_cs ! (off + m + blen) = fqmul_int ?D zi\<close>
      unfolding inv_cs_def by (rule invntt_inner_loop_int_high_val[OF im2 assms(3) off_bound])
    have \<open>ntt_inner_loop_int zf off blen cnt inv_cs ! (off + m + blen) mod MLKEM_Q =
          (barrett_reduce_int (?a + ?b) - fqmul_int (fqmul_int ?D zi) zf) mod MLKEM_Q\<close>
      using ntt_val inv_low inv_high by simp
    also have \<open>\<dots> = ((?a + ?b) - ?D * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
      by (rule mod_diff_cong[OF barrett_reduce_mod fqmul_fqmul_cancel[OF assms(5,6,4)]])
    also have \<open>\<dots> = 2 * ?b mod MLKEM_Q\<close>
      by (simp add: mod_eq_dvd_iff algebra_simps)
    finally show ?thesis
      using im1 im2 not_low by (simp add: inv_cs_def)
  qed
  have case_out: \<open>i \<notin> {off..<off+cnt} \<Longrightarrow> i \<notin> {off+blen..<off+cnt+blen} \<Longrightarrow> ?thesis\<close>
  proof -
    assume nl: \<open>i \<notin> {off..<off+cnt}\<close> and nh: \<open>i \<notin> {off+blen..<off+cnt+blen}\<close>
    have \<open>ntt_inner_loop_int zf off blen cnt inv_cs ! i = inv_cs ! i\<close>
      by (rule ntt_inner_loop_int_nth_unchanged) (use nl nh in auto)
    also have \<open>\<dots> = cs ! i\<close>
      unfolding inv_cs_def by (rule invntt_inner_loop_int_nth_unchanged) (use nl nh in auto)
    finally show ?thesis
      using nl nh by (auto simp: inv_cs_def)
  qed
  show ?thesis
    using case_low case_high case_out by blast
qed

lemma inner_loop_composition_ntt_invntt:
  assumes \<open>length cs = MLKEM_N\<close>
      and \<open>off + 2 * blen \<le> MLKEM_N\<close>
      and \<open>cnt \<le> blen\<close>
      and \<open>mlkem_zeta ^ br_fwd * mlkem_zeta ^ br_inv mod MLKEM_Q = MLKEM_Q - 1\<close>
      and \<open>zf mod MLKEM_Q = mlkem_zeta ^ br_fwd * 2^16 mod MLKEM_Q\<close>
      and \<open>zi mod MLKEM_Q = mlkem_zeta ^ br_inv * 2^16 mod MLKEM_Q\<close>
      and \<open>i < length cs\<close>
    shows \<open>invntt_inner_loop_int zi off blen cnt (ntt_inner_loop_int zf off blen cnt cs) ! i mod MLKEM_Q =
             (if i \<in> {off..<off+cnt} \<or> i \<in> {off+blen..<off+cnt+blen} then
                2 * cs ! i mod MLKEM_Q
              else
                cs ! i mod MLKEM_Q)\<close>
proof -
  define ntt_cs where
    \<open>ntt_cs = ntt_inner_loop_int zf off blen cnt cs\<close>
  have len_ntt: \<open>length ntt_cs = length cs\<close>
    by (simp add: ntt_cs_def ntt_inner_loop_int_length)
  have off_bound: \<open>off + 2 * blen \<le> length cs\<close>
    using assms(1,2) by simp
  have case_low: \<open>i \<in> {off..<off+cnt} \<Longrightarrow> ?thesis\<close>
  proof -
    assume low: \<open>i \<in> {off..<off+cnt}\<close>
    define m where
      \<open>m = i - off\<close>
    let ?a = \<open>cs ! (off + m)\<close>
    let ?b = \<open>cs ! (off + m + blen)\<close>
    have im1: \<open>i = off + m\<close> and im2: \<open>m < cnt\<close>
      using low by (auto simp: m_def)
    have ntt_low: \<open>ntt_cs ! (off + m) = ?a + fqmul_int ?b zf\<close>
      unfolding ntt_cs_def by (rule ntt_inner_loop_int_low_val[OF im2 assms(3) off_bound])
    have ntt_high: \<open>ntt_cs ! (off + m + blen) = ?a - fqmul_int ?b zf\<close>
      unfolding ntt_cs_def by (rule ntt_inner_loop_int_high_val[OF im2 assms(3) off_bound])
    have inv_val: \<open>invntt_inner_loop_int zi off blen cnt ntt_cs ! (off + m) =
          barrett_reduce_int (ntt_cs ! (off + m) + ntt_cs ! (off + m + blen))\<close>
      by (rule invntt_inner_loop_int_low_val[OF im2 assms(3)])
          (use len_ntt off_bound in simp)
    have sum_eq: \<open>ntt_cs ! (off + m) + ntt_cs ! (off + m + blen) = 2 * ?a\<close>
      using ntt_low ntt_high by simp
    have \<open>invntt_inner_loop_int zi off blen cnt ntt_cs ! (off + m) mod MLKEM_Q =
          barrett_reduce_int (2 * ?a) mod MLKEM_Q\<close>
      using inv_val sum_eq by simp
    also have \<open>\<dots> = 2 * ?a mod MLKEM_Q\<close>
      by (rule barrett_reduce_mod)
    finally show ?thesis
      using im1 im2 low by (simp add: ntt_cs_def)
  qed
  have case_high: \<open>i \<in> {off+blen..<off+cnt+blen} \<Longrightarrow> i \<notin> {off..<off+cnt} \<Longrightarrow> ?thesis\<close>
  proof -
    assume high: \<open>i \<in> {off+blen..<off+cnt+blen}\<close>
       and not_low: \<open>i \<notin> {off..<off+cnt}\<close>
    define m where
      \<open>m = i - off - blen\<close>
    let ?a = \<open>cs ! (off + m)\<close>
    let ?b = \<open>cs ! (off + m + blen)\<close>
    let ?Zf = \<open>mlkem_zeta ^ br_fwd\<close>
    let ?Zi = \<open>mlkem_zeta ^ br_inv\<close>
    have im1: \<open>i = off + m + blen\<close> and im2: \<open>m < cnt\<close>
      using high assms(3) by (auto simp: m_def)
    have ntt_low: \<open>ntt_cs ! (off + m) = ?a + fqmul_int ?b zf\<close>
      unfolding ntt_cs_def by (rule ntt_inner_loop_int_low_val[OF im2 assms(3) off_bound])
    have ntt_high: \<open>ntt_cs ! (off + m + blen) = ?a - fqmul_int ?b zf\<close>
      unfolding ntt_cs_def by (rule ntt_inner_loop_int_high_val[OF im2 assms(3) off_bound])
    have inv_val: \<open>invntt_inner_loop_int zi off blen cnt ntt_cs ! (off + m + blen) =
          fqmul_int (ntt_cs ! (off + m + blen) - ntt_cs ! (off + m)) zi\<close>
      by (rule invntt_inner_loop_int_high_val[OF im2 assms(3)])
         (use len_ntt off_bound in simp)
    have diff_eq: \<open>ntt_cs ! (off + m + blen) - ntt_cs ! (off + m) = - 2 * fqmul_int ?b zf\<close>
      using ntt_low ntt_high by simp
    have fqmul_cancel: \<open>fqmul_int ?b zf mod MLKEM_Q = ?b * ?Zf mod MLKEM_Q\<close>
      by (rule fqmul_zeta_cancel[OF assms(5)])
    have neg2_Q_mod: \<open>(-2) * (x::int) * (MLKEM_Q - 1) mod MLKEM_Q = 2 * x mod MLKEM_Q\<close> for x
      by (simp add: mod_eq_dvd_iff algebra_simps)
    have key: \<open>fqmul_int (- 2 * fqmul_int ?b zf) zi mod MLKEM_Q = 2 * ?b mod MLKEM_Q\<close>
    proof -
      have \<open>fqmul_int (- 2 * fqmul_int ?b zf) zi mod MLKEM_Q =
            (- 2 * fqmul_int ?b zf) * ?Zi mod MLKEM_Q\<close>
        by (rule fqmul_zeta_cancel[OF assms(6)])
      also have \<open>\<dots> = (-2) * (?b * ?Zf) * ?Zi mod MLKEM_Q\<close>
      proof -
        have \<open>(- 2 * fqmul_int ?b zf) * ?Zi mod MLKEM_Q =
              ((- 2 * fqmul_int ?b zf mod MLKEM_Q) * ?Zi) mod MLKEM_Q\<close>
          by (rule mod_mult_left_eq[symmetric])
        also have \<open>- 2 * fqmul_int ?b zf mod MLKEM_Q = (- 2) * (?b * ?Zf) mod MLKEM_Q\<close>
        proof -
          have \<open>- 2 * fqmul_int ?b zf mod MLKEM_Q =
                ((- 2) * (fqmul_int ?b zf mod MLKEM_Q)) mod MLKEM_Q\<close>
            by (rule mod_mult_right_eq[symmetric])
          also have \<open>\<dots> = ((- 2) * (?b * ?Zf mod MLKEM_Q)) mod MLKEM_Q\<close>
            using fqmul_cancel by simp
          also have \<open>\<dots> = (- 2) * (?b * ?Zf) mod MLKEM_Q\<close>
            by (rule mod_mult_right_eq)
          finally show ?thesis .
        qed
        hence \<open>((- 2 * fqmul_int ?b zf mod MLKEM_Q) * ?Zi) mod MLKEM_Q =
               (((- 2) * (?b * ?Zf) mod MLKEM_Q) * ?Zi) mod MLKEM_Q\<close>
          by simp
        also have \<open>\<dots> = ((- 2) * (?b * ?Zf) * ?Zi) mod MLKEM_Q\<close>
          by (rule mod_mult_left_eq)
        finally show ?thesis
          by simp
      qed
      also have \<open>\<dots> = (-2) * ?b * (?Zf * ?Zi) mod MLKEM_Q\<close>
        by (simp add: algebra_simps)
      also have \<open>\<dots> = (-2) * ?b * (MLKEM_Q - 1) mod MLKEM_Q\<close>
      proof -
        have \<open>(-2) * ?b * (?Zf * ?Zi) mod MLKEM_Q =
              ((-2) * ?b * (?Zf * ?Zi mod MLKEM_Q)) mod MLKEM_Q\<close>
          by (rule mod_mult_right_eq[symmetric])
        also have \<open>\<dots> = ((-2) * ?b * (MLKEM_Q - 1)) mod MLKEM_Q\<close>
          using assms(4) by simp
        finally show ?thesis .
      qed
      also have \<open>\<dots> = 2 * ?b mod MLKEM_Q\<close>
        by (rule neg2_Q_mod)
      finally show ?thesis .
    qed
    have \<open>invntt_inner_loop_int zi off blen cnt ntt_cs ! (off + m + blen) mod MLKEM_Q =
          fqmul_int (- 2 * fqmul_int ?b zf) zi mod MLKEM_Q\<close>
      using inv_val diff_eq by simp
    also have \<open>\<dots> = 2 * ?b mod MLKEM_Q\<close>
      by (rule key)
    finally show ?thesis
      using im1 im2 not_low by (simp add: ntt_cs_def)
  qed
  have case_out: \<open>i \<notin> {off..<off+cnt} \<Longrightarrow> i \<notin> {off+blen..<off+cnt+blen} \<Longrightarrow> ?thesis\<close>
  proof -
    assume nl: \<open>i \<notin> {off..<off+cnt}\<close>
       and nh: \<open>i \<notin> {off+blen..<off+cnt+blen}\<close>
    have \<open>invntt_inner_loop_int zi off blen cnt ntt_cs ! i = ntt_cs ! i\<close>
      by (rule invntt_inner_loop_int_nth_unchanged) (use nl nh in auto)
    also have \<open>\<dots> = cs ! i\<close>
      unfolding ntt_cs_def by (rule ntt_inner_loop_int_nth_unchanged) (use nl nh in auto)
    finally show ?thesis
      using nl nh by (auto simp: ntt_cs_def)
  qed
  show ?thesis
    using case_low case_high case_out by blast
qed

subsection \<open>Tier 5 — Layer-Level Inverse\<close>

text \<open>A full NTT layer composed with the corresponding inverse NTT layer
  (or vice versa) scales every coefficient by 2 mod Q.\<close>

text \<open>Inner loop congruence: if two lists agree on the block positions,
  the inner loop results agree on those positions.\<close>

lemma ntt_inner_loop_int_cong:
  assumes agree: \<open>\<forall>p. off \<le> p \<longrightarrow> p < off + 2 * blen \<longrightarrow> xs ! p = ys ! p\<close>
      and len_xs: \<open>off + 2 * blen \<le> length xs\<close>
      and len_ys: \<open>off + 2 * blen \<le> length ys\<close>
      and i_lo: \<open>off \<le> i\<close>
      and i_hi: \<open>i < off + 2 * blen\<close>
    shows \<open>ntt_inner_loop_int z off blen blen xs ! i =
           ntt_inner_loop_int z off blen blen ys ! i\<close>
proof (cases \<open>i < off + blen\<close>)
  case True
  define m where
    \<open>m = i - off\<close>
  have im: \<open>i = off + m\<close> and mb: \<open>m < blen\<close>
    using i_lo True by (auto simp: m_def)
  have eq1: \<open>xs ! (off + m) = ys ! (off + m)\<close>
    using agree mb by auto
  have eq2: \<open>xs ! (off + m + blen) = ys ! (off + m + blen)\<close>
    using agree mb by auto
  show ?thesis unfolding im
    using ntt_inner_loop_int_low_val[OF mb le_refl len_xs]
          ntt_inner_loop_int_low_val[OF mb le_refl len_ys] eq1 eq2 by simp
next
  case False
  define m where
    \<open>m = i - off - blen\<close>
  have im: \<open>i = off + m + blen\<close> and mb: \<open>m < blen\<close>
    using i_lo i_hi False by (auto simp: m_def)
  have eq1: \<open>xs ! (off + m) = ys ! (off + m)\<close>
    using agree mb by auto
  have eq2: \<open>xs ! (off + m + blen) = ys ! (off + m + blen)\<close>
    using agree mb by auto
  show ?thesis unfolding im
    using ntt_inner_loop_int_high_val[OF mb le_refl len_xs]
          ntt_inner_loop_int_high_val[OF mb le_refl len_ys] eq1 eq2 by simp
qed

lemma invntt_inner_loop_int_cong:
  assumes agree: \<open>\<forall>p. off \<le> p \<longrightarrow> p < off + 2 * blen \<longrightarrow> xs ! p = ys ! p\<close>
      and len_xs: \<open>off + 2 * blen \<le> length xs\<close>
      and len_ys: \<open>off + 2 * blen \<le> length ys\<close>
      and i_lo: \<open>off \<le> i\<close>
      and i_hi: \<open>i < off + 2 * blen\<close>
    shows \<open>invntt_inner_loop_int z off blen blen xs ! i =
           invntt_inner_loop_int z off blen blen ys ! i\<close>
proof (cases \<open>i < off + blen\<close>)
  case True
  define m where
    \<open>m = i - off\<close>
  have im: \<open>i = off + m\<close> and mb: \<open>m < blen\<close>
    using i_lo True by (auto simp: m_def)
  have eq1: \<open>xs ! (off + m) = ys ! (off + m)\<close>
    using agree mb by auto
  have eq2: \<open>xs ! (off + m + blen) = ys ! (off + m + blen)\<close>
    using agree mb by auto
  show ?thesis
    unfolding im using invntt_inner_loop_int_low_val[OF mb le_refl len_xs]
          invntt_inner_loop_int_low_val[OF mb le_refl len_ys] eq1 eq2 by simp
next
  case False
  define m where
    \<open>m = i - off - blen\<close>
  have im: \<open>i = off + m + blen\<close> and mb: \<open>m < blen\<close>
    using i_lo i_hi False by (auto simp: m_def)
  have eq1: \<open>xs ! (off + m) = ys ! (off + m)\<close>
    using agree mb by auto
  have eq2: \<open>xs ! (off + m + blen) = ys ! (off + m + blen)\<close>
    using agree mb by auto
  show ?thesis
    unfolding im using invntt_inner_loop_int_high_val[OF mb le_refl len_xs]
          invntt_inner_loop_int_high_val[OF mb le_refl len_ys] eq1 eq2 by simp
qed

text \<open>Middle loop block decomposition: the full middle loop at a position
  in block j equals just the inner loop for block j applied to the original list.\<close>

lemma ntt_middle_loop_at_block:
  assumes \<open>j < nb\<close> \<open>nb * (2 * blen) \<le> length cs\<close>
      and \<open>j * (2 * blen) \<le> i\<close>
      and \<open>i < Suc j * (2 * blen)\<close>
    shows \<open>snd (ntt_middle_loop_int k blen nb nb cs) ! i =
           ntt_inner_loop_int (zetas_int ! (k + j)) (j * (2 * blen)) blen blen cs ! i\<close>
using assms proof (induction nb arbitrary: k cs)
  case 0 then
    show ?case by simp
next
  case (Suc nb')
  have snoc: \<open>snd (ntt_middle_loop_int k blen (Suc nb') (Suc nb') cs) =
    ntt_inner_loop_int (zetas_int ! (k + nb')) (nb' * (2 * blen)) blen blen
      (snd (ntt_middle_loop_int k blen nb' nb' cs))\<close>
    by (rule ntt_middle_loop_int_snoc)
  show ?case
  proof (cases \<open>j < nb'\<close>)
    case True
    hence \<open>Suc j \<le> nb'\<close>
      by simp
    hence \<open>Suc j * (2 * blen) \<le> nb' * (2 * blen)\<close>
      by (rule mult_le_mono1)
    with Suc.prems(4) have i_bound: \<open>i < nb' * (2 * blen)\<close> by simp
    have i_not_lo: \<open>i \<notin> {nb' * (2 * blen)..<nb' * (2 * blen) + blen}\<close>
      using i_bound by auto
    have i_not_hi: \<open>i \<notin> {nb' * (2 * blen) + blen..<nb' * (2 * blen) + blen + blen}\<close>
      using i_bound by auto
    have len_nb': \<open>nb' * (2 * blen) \<le> length cs\<close>
      using Suc.prems(2) by simp
    have \<open>snd (ntt_middle_loop_int k blen (Suc nb') (Suc nb') cs) ! i =
          snd (ntt_middle_loop_int k blen nb' nb' cs) ! i\<close>
      unfolding snoc by (rule ntt_inner_loop_int_nth_unchanged[OF i_not_lo i_not_hi])
    also have \<open>\<dots> = ntt_inner_loop_int (zetas_int ! (k + j)) (j * (2 * blen)) blen blen cs ! i\<close>
      by (rule Suc.IH[OF True len_nb' Suc.prems(3) Suc.prems(4)])
    finally show ?thesis .
  next
    case False
    hence j_eq: \<open>j = nb'\<close> using Suc.prems(1)
      by simp
    define prev where
      \<open>prev = snd (ntt_middle_loop_int k blen nb' nb' cs)\<close>
    have agree: \<open>\<forall>p. nb' * (2 * blen) \<le> p \<longrightarrow> p < nb' * (2 * blen) + 2 * blen \<longrightarrow> prev ! p = cs ! p\<close>
    proof (intro allI impI)
         fix p
      assume \<open>nb' * (2 * blen) \<le> p\<close> \<open>p < nb' * (2 * blen) + 2 * blen\<close>
        show \<open>prev ! p = cs ! p\<close>
        unfolding prev_def by (rule ntt_middle_loop_int_nth_unchanged[OF \<open>nb' * (2 * blen) \<le> p\<close>])
    qed
    have len_prev: \<open>nb' * (2 * blen) + 2 * blen \<le> length prev\<close>
      unfolding prev_def using Suc.prems(2) by (simp add: ntt_middle_loop_int_length)
    have len_cs: \<open>nb' * (2 * blen) + 2 * blen \<le> length cs\<close>
      using Suc.prems(2) by simp
    show ?thesis
      unfolding snoc j_eq prev_def[symmetric]
      by (rule ntt_inner_loop_int_cong[OF agree len_prev len_cs])
         (use Suc.prems(3,4) j_eq in auto)
  qed
qed

lemma invntt_middle_loop_at_block:
  assumes \<open>j < nb\<close> \<open>nb * (2 * blen) \<le> length cs\<close>
      and \<open>j * (2 * blen) \<le> i\<close>
      and \<open>i < Suc j * (2 * blen)\<close>
    shows \<open>snd (invntt_middle_loop_int k blen nb nb cs) ! i =
           invntt_inner_loop_int (zetas_int ! (k - j)) (j * (2 * blen)) blen blen cs ! i\<close>
using assms proof (induction nb arbitrary: k cs)
  case 0
  then show ?case by simp
next
  case (Suc nb')
  have snoc: \<open>snd (invntt_middle_loop_int k blen (Suc nb') (Suc nb') cs) =
    invntt_inner_loop_int (zetas_int ! (k - nb')) (nb' * (2 * blen)) blen blen
      (snd (invntt_middle_loop_int k blen nb' nb' cs))\<close>
    by (rule invntt_middle_loop_int_snoc)
  show ?case
  proof (cases \<open>j < nb'\<close>)
    case True
    hence \<open>Suc j \<le> nb'\<close>
      by simp
    hence \<open>Suc j * (2 * blen) \<le> nb' * (2 * blen)\<close>
      by (rule mult_le_mono1)
    with Suc.prems(4) have i_bound: \<open>i < nb' * (2 * blen)\<close>
      by simp
    have i_not_lo: \<open>i \<notin> {nb' * (2 * blen)..<nb' * (2 * blen) + blen}\<close>
      using i_bound by auto
    have i_not_hi: \<open>i \<notin> {nb' * (2 * blen) + blen..<nb' * (2 * blen) + blen + blen}\<close>
      using i_bound by auto
    have len_nb': \<open>nb' * (2 * blen) \<le> length cs\<close>
      using Suc.prems(2) by simp
    have \<open>snd (invntt_middle_loop_int k blen (Suc nb') (Suc nb') cs) ! i =
          snd (invntt_middle_loop_int k blen nb' nb' cs) ! i\<close>
      unfolding snoc by (rule invntt_inner_loop_int_nth_unchanged[OF i_not_lo i_not_hi])
    also have \<open>\<dots> = invntt_inner_loop_int (zetas_int ! (k - j)) (j * (2 * blen)) blen blen cs ! i\<close>
      by (rule Suc.IH[OF True len_nb' Suc.prems(3) Suc.prems(4)])
    finally show ?thesis .
  next
    case False
    hence j_eq: \<open>j = nb'\<close>
      using Suc.prems(1) by simp
    define prev where
      \<open>prev = snd (invntt_middle_loop_int k blen nb' nb' cs)\<close>
    have agree: \<open>\<forall>p. nb' * (2 * blen) \<le> p \<longrightarrow> p < nb' * (2 * blen) + 2 * blen \<longrightarrow> prev ! p = cs ! p\<close>
    proof (intro allI impI)
         fix p
      assume \<open>nb' * (2 * blen) \<le> p\<close> \<open>p < nb' * (2 * blen) + 2 * blen\<close>
        show \<open>prev ! p = cs ! p\<close>
        unfolding prev_def by (rule invntt_middle_loop_int_nth_unchanged[OF \<open>nb' * (2 * blen) \<le> p\<close>])
    qed
    have len_prev: \<open>nb' * (2 * blen) + 2 * blen \<le> length prev\<close>
      unfolding prev_def using Suc.prems(2) by (simp add: invntt_middle_loop_int_length)
    have len_cs: \<open>nb' * (2 * blen) + 2 * blen \<le> length cs\<close>
      using Suc.prems(2) by simp
    show ?thesis
      unfolding snoc j_eq prev_def[symmetric]
      by (rule invntt_inner_loop_int_cong[OF agree len_prev len_cs])
         (use Suc.prems(3,4) j_eq in auto)
  qed
qed

text \<open>Arithmetic helper: the number of blocks times the block size equals @{text MLKEM_N}.\<close>

lemma ntt_nb_blen_eq:
  assumes \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
    shows \<open>(2::nat)^(l-1) * (2 * 2^(8-l)) = MLKEM_N\<close>
proof -
  have \<open>(2::nat)^(l-1) * (2 * 2^(8-l)) = 2^(l-1) * 2^(9-l)\<close>
  proof -
    have \<open>(9::nat) - l = Suc (8 - l)\<close>
      using assms by auto
    thus ?thesis
      by simp
  qed
  also have \<open>\<dots> = (2::nat)^((l-1) + (9-l))\<close>
    by (simp add: power_add)
  also have \<open>(l-1) + (9-l) = (8::nat)\<close>
    using assms by auto
  finally show ?thesis
    by simp
qed

lemma ntt_invntt_layer_inverse:
  assumes \<open>length cs = MLKEM_N\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>i < MLKEM_N\<close>
    shows \<open>ntt_layer_int l (invntt_layer_int l cs) ! i mod MLKEM_Q =
             2 * cs ! i mod MLKEM_Q\<close>
proof -
  define nb where
    \<open>nb = (2::nat)^(l-1)\<close>
  define blen where
    \<open>blen = (2::nat)^(8-l)\<close>
  define inv_cs where
    \<open>inv_cs = invntt_layer_int l cs\<close>
  define j where
    \<open>j = i div (2 * blen)\<close>
  define ki where
    \<open>ki = (2::nat)^l - 1 - j\<close>
  define local_inv where
    \<open>local_inv = invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen cs\<close>
  have nb_blen: \<open>nb * (2 * blen) = MLKEM_N\<close>
    using ntt_nb_blen_eq[OF assms(2) assms(3)] by (simp add: nb_def blen_def)
  have i_lt: \<open>i < nb * (2 * blen)\<close>
    using assms(4) nb_blen by linarith
  have j_lt_nb: \<open>j < nb\<close>
    unfolding j_def using i_lt by (simp add: less_mult_imp_div_less)
  have sj_le_nb: \<open>Suc j \<le> nb\<close>
    using j_lt_nb by simp
  have sj_le: \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
    by (rule mult_le_mono1[OF sj_le_nb])
  have j_lo: \<open>j * (2 * blen) \<le> i\<close>
    unfolding j_def by simp
  have j_hi_aux: \<open>i < j * (2 * blen) + 2 * blen\<close>
  proof -
    have blen_pos: \<open>(0::nat) < 2 * blen\<close>
      by (simp add: blen_def)
    have mod_bound: \<open>i mod (2 * blen) < 2 * blen\<close>
      using blen_pos by simp
    have eq: \<open>i div (2 * blen) * (2 * blen) + i mod (2 * blen) = i\<close>
      by (rule div_mult_mod_eq)
    show ?thesis unfolding j_def using mod_bound eq by linarith
  qed
  hence j_hi: \<open>i < Suc j * (2 * blen)\<close>
    by simp
  have len_cs: \<open>length cs = MLKEM_N\<close>
    by (rule assms(1))
  have block_len_cs: \<open>j * (2 * blen) + 2 * blen \<le> length cs\<close>
    using sj_le nb_blen len_cs by simp
  have off_bound: \<open>j * (2 * blen) + 2 * blen \<le> MLKEM_N\<close>
    using block_len_cs assms(1) by simp
  have l_suc: \<open>Suc (l - 1) = l\<close>
    using assms(2) by simp
  have two_nb: \<open>2 * nb = 2^l\<close>
  proof -
    have \<open>(2::nat) * 2^(l-1) = 2^Suc (l-1)\<close> by simp
    also have \<open>Suc (l-1) = l\<close> using assms(2) by simp
    finally show ?thesis by (simp add: nb_def)
  qed
  have l_le_8: \<open>l \<le> 8\<close>
    using assms(3) by simp
  have two_l_le: \<open>(2::nat)^l \<le> 128\<close>
  proof -
    have \<open>(2::nat)^l \<le> 2^7\<close>
      by (rule power_increasing) (use assms(3) in auto)
    thus ?thesis by simp
  qed
  have nb_j_lt: \<open>nb + j < 128\<close>
    using j_lt_nb two_nb two_l_le by linarith
  have ki_bound: \<open>ki < 2^l\<close>
    unfolding ki_def using j_lt_nb two_nb by linarith
  have ki_j_lt: \<open>ki < 128\<close>
    using ki_bound two_l_le by linarith
  have ki_eq: \<open>ki = 2^l - 1 - j\<close>
    unfolding ki_def by simp
  have j_lt_pow: \<open>j < 2^(l-1)\<close>
    using j_lt_nb nb_def by simp
  have ntt_decomp: \<open>ntt_layer_int l inv_cs ! i =
    ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen inv_cs ! i\<close>
  proof -
    have \<open>snd (ntt_middle_loop_int nb blen nb nb inv_cs) ! i =
      ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen inv_cs ! i\<close>
      by (rule ntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen inv_cs_def invntt_layer_int_length assms(1))
    thus ?thesis
      by (simp add: ntt_layer_int_def nb_def blen_def inv_cs_def)
  qed
  have inv_agree: \<open>inv_cs ! p = local_inv ! p\<close>
    if \<open>j * (2 * blen) \<le> p\<close> \<open>p < j * (2 * blen) + 2 * blen\<close> for p
  proof -
    have step1: \<open>snd (invntt_middle_loop_int (2^l - 1) blen nb nb cs) ! p =
      invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen cs ! p\<close>
      by (rule invntt_middle_loop_at_block[OF j_lt_nb _ that(1)])
         (use nb_blen len_cs in simp, use that(2) in simp)
    have \<open>invntt_layer_int l cs ! p =
      invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen cs ! p\<close>
      using step1 by (simp add: invntt_layer_int_def nb_def blen_def ki_def)
    thus ?thesis
      by (simp add: inv_cs_def local_inv_def)
  qed
  have cong_step: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen inv_cs ! i =
    ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen local_inv ! i\<close>
  proof (rule ntt_inner_loop_int_cong[OF _ _ _ j_lo])
    show \<open>\<forall>p. j * (2 * blen) \<le> p \<longrightarrow> p < j * (2 * blen) + 2 * blen \<longrightarrow> inv_cs ! p = local_inv ! p\<close>
      using inv_agree by blast
    show \<open>j * (2 * blen) + 2 * blen \<le> length inv_cs\<close>
      unfolding inv_cs_def using invntt_layer_int_length assms(1) off_bound by simp
    show \<open>j * (2 * blen) + 2 * blen \<le> length local_inv\<close>
      unfolding local_inv_def using invntt_inner_loop_int_length assms(1) off_bound by simp
    show \<open>i < j * (2 * blen) + 2 * blen\<close>
      using j_hi_aux by simp
  qed
  have br_sum: \<open>bit_reverse 7 (nb + j) + bit_reverse 7 ki = 128\<close>
    unfolding nb_def ki_eq
    by (rule bit_reverse_complement[OF j_lt_pow assms(2) assms(3)])
  have zeta_cancel: \<open>mlkem_zeta ^ bit_reverse 7 (nb + j) * mlkem_zeta ^ bit_reverse 7 ki mod MLKEM_Q = MLKEM_Q - 1\<close>
    by (rule zeta_power_sum_128[OF br_sum])
  have zf_mod: \<open>zetas_int ! (nb + j) mod MLKEM_Q = mlkem_zeta ^ bit_reverse 7 (nb + j) * 2^16 mod MLKEM_Q\<close>
    by (rule zetas_int_mod[OF nb_j_lt])
  have zi_mod: \<open>zetas_int ! ki mod MLKEM_Q = mlkem_zeta ^ bit_reverse 7 ki * 2^16 mod MLKEM_Q\<close>
    by (rule zetas_int_mod[OF ki_j_lt])
  have i_lt_cs: \<open>i < length cs\<close>
    using assms(1) assms(4) by simp
  have comp: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen local_inv ! i mod MLKEM_Q =
    2 * cs ! i mod MLKEM_Q\<close>
  proof -
    have \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen
           (invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen cs) ! i mod MLKEM_Q =
      (if i \<in> {j * (2 * blen)..<j * (2 * blen) + blen} \<or>
          i \<in> {j * (2 * blen) + blen..<j * (2 * blen) + blen + blen}
       then 2 * cs ! i mod MLKEM_Q
       else cs ! i mod MLKEM_Q)\<close>
      by (rule inner_loop_composition_invntt_ntt[OF assms(1) off_bound le_refl
            zeta_cancel zf_mod zi_mod i_lt_cs])
    moreover have \<open>i \<in> {j * (2 * blen)..<j * (2 * blen) + blen} \<or>
          i \<in> {j * (2 * blen) + blen..<j * (2 * blen) + blen + blen}\<close>
      using j_lo j_hi_aux by auto
    ultimately show ?thesis
      unfolding local_inv_def by simp
  qed
  have \<open>ntt_layer_int l (invntt_layer_int l cs) ! i mod MLKEM_Q =
    ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen local_inv ! i mod MLKEM_Q\<close>
    unfolding inv_cs_def[symmetric] using ntt_decomp cong_step by simp
  also have \<open>\<dots> = 2 * cs ! i mod MLKEM_Q\<close>
    by (rule comp)
  finally show ?thesis .
qed

lemma invntt_ntt_layer_inverse:
  assumes \<open>length cs = MLKEM_N\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>i < MLKEM_N\<close>
    shows \<open>invntt_layer_int l (ntt_layer_int l cs) ! i mod MLKEM_Q =
             2 * cs ! i mod MLKEM_Q\<close>
proof -
  define nb where
    \<open>nb = (2::nat)^(l-1)\<close>
  define blen where
    \<open>blen = (2::nat)^(8-l)\<close>
  define ntt_cs where
    \<open>ntt_cs = ntt_layer_int l cs\<close>
  define j where
    \<open>j = i div (2 * blen)\<close>
  define ki where
    \<open>ki = (2::nat)^l - 1 - j\<close>
  define local_ntt where
    \<open>local_ntt = ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs\<close>
  have nb_blen: \<open>nb * (2 * blen) = MLKEM_N\<close>
    using ntt_nb_blen_eq[OF assms(2) assms(3)] by (simp add: nb_def blen_def)
  have i_lt: \<open>i < nb * (2 * blen)\<close>
    using assms(4) nb_blen by linarith
  have j_lt_nb: \<open>j < nb\<close>
    unfolding j_def using i_lt by (simp add: less_mult_imp_div_less)
  have sj_le_nb: \<open>Suc j \<le> nb\<close>
    using j_lt_nb by simp
  have sj_le: \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
    by (rule mult_le_mono1[OF sj_le_nb])
  have j_lo: \<open>j * (2 * blen) \<le> i\<close>
    unfolding j_def by simp
  have j_hi_aux: \<open>i < j * (2 * blen) + 2 * blen\<close>
  proof -
    have blen_pos: \<open>(0::nat) < 2 * blen\<close>
      by (simp add: blen_def)
    have mod_bound: \<open>i mod (2 * blen) < 2 * blen\<close>
      using blen_pos by simp
    have eq: \<open>i div (2 * blen) * (2 * blen) + i mod (2 * blen) = i\<close>
      by (rule div_mult_mod_eq)
    show ?thesis
      unfolding j_def using mod_bound eq by linarith
  qed
  hence j_hi: \<open>i < Suc j * (2 * blen)\<close>
    by simp
  have len_cs: \<open>length cs = MLKEM_N\<close>
    by (rule assms(1))
  have block_len_cs: \<open>j * (2 * blen) + 2 * blen \<le> length cs\<close>
    using sj_le nb_blen len_cs by simp
  have off_bound: \<open>j * (2 * blen) + 2 * blen \<le> MLKEM_N\<close>
    using block_len_cs assms(1) by simp
  have l_suc: \<open>Suc (l - 1) = l\<close>
    using assms(2) by simp
  have two_nb: \<open>2 * nb = 2^l\<close>
  proof -
    have \<open>(2::nat) * 2^(l-1) = 2^Suc (l-1)\<close>
      by simp
    also have \<open>Suc (l-1) = l\<close>
      using assms(2) by simp
    finally show ?thesis
      by (simp add: nb_def)
  qed
  have two_l_le: \<open>(2::nat)^l \<le> 128\<close>
  proof -
    have \<open>(2::nat)^l \<le> 2^7\<close>
      by (rule power_increasing) (use assms(3) in auto)
    thus ?thesis
      by simp
  qed
  have nb_j_lt: \<open>nb + j < 128\<close>
    using j_lt_nb two_nb two_l_le by linarith
  have ki_bound: \<open>ki < 2^l\<close>
    unfolding ki_def using j_lt_nb two_nb by linarith
  have ki_j_lt: \<open>ki < 128\<close>
    using ki_bound two_l_le by linarith
  have ki_eq: \<open>ki = 2^l - 1 - j\<close>
    unfolding ki_def by simp
  have j_lt_pow: \<open>j < 2^(l-1)\<close>
    using j_lt_nb nb_def by simp
  have invntt_decomp: \<open>invntt_layer_int l ntt_cs ! i =
    invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen ntt_cs ! i\<close>
  proof -
    have step1: \<open>snd (invntt_middle_loop_int (2^l - 1) blen nb nb ntt_cs) ! i =
      invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen ntt_cs ! i\<close>
      by (rule invntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen ntt_cs_def ntt_layer_int_length assms(1))
    thus ?thesis
      by (simp add: invntt_layer_int_def nb_def blen_def ntt_cs_def ki_def)
  qed
  have ntt_agree: \<open>ntt_cs ! p = local_ntt ! p\<close>
    if \<open>j * (2 * blen) \<le> p\<close> \<open>p < j * (2 * blen) + 2 * blen\<close> for p
  proof -
    have step1: \<open>snd (ntt_middle_loop_int nb blen nb nb cs) ! p =
      ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs ! p\<close>
      by (rule ntt_middle_loop_at_block[OF j_lt_nb _ that(1)])
         (use nb_blen len_cs in simp, use that(2) in simp)
    have \<open>ntt_layer_int l cs ! p =
      ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs ! p\<close>
      using step1 by (simp add: ntt_layer_int_def nb_def blen_def)
    thus ?thesis
      by (simp add: ntt_cs_def local_ntt_def)
  qed
  have cong_step: \<open>invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen ntt_cs ! i =
    invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen local_ntt ! i\<close>
  proof (rule invntt_inner_loop_int_cong[OF _ _ _ j_lo])
    show \<open>\<forall>p. j * (2 * blen) \<le> p \<longrightarrow> p < j * (2 * blen) + 2 * blen \<longrightarrow> ntt_cs ! p = local_ntt ! p\<close>
      using ntt_agree by blast
    show \<open>j * (2 * blen) + 2 * blen \<le> length ntt_cs\<close>
      unfolding ntt_cs_def using ntt_layer_int_length assms(1) off_bound by simp
    show \<open>j * (2 * blen) + 2 * blen \<le> length local_ntt\<close>
      unfolding local_ntt_def using ntt_inner_loop_int_length assms(1) off_bound by simp
    show \<open>i < j * (2 * blen) + 2 * blen\<close>
      using j_hi_aux by simp
  qed
  have br_sum: \<open>bit_reverse 7 (nb + j) + bit_reverse 7 ki = 128\<close>
    unfolding nb_def ki_eq by (rule bit_reverse_complement[OF j_lt_pow assms(2) assms(3)])
  have zeta_cancel: \<open>mlkem_zeta ^ bit_reverse 7 (nb + j) * mlkem_zeta ^ bit_reverse 7 ki mod MLKEM_Q = MLKEM_Q - 1\<close>
    by (rule zeta_power_sum_128[OF br_sum])
  have zf_mod: \<open>zetas_int ! (nb + j) mod MLKEM_Q = mlkem_zeta ^ bit_reverse 7 (nb + j) * 2^16 mod MLKEM_Q\<close>
    by (rule zetas_int_mod[OF nb_j_lt])
  have zi_mod: \<open>zetas_int ! ki mod MLKEM_Q = mlkem_zeta ^ bit_reverse 7 ki * 2^16 mod MLKEM_Q\<close>
    by (rule zetas_int_mod[OF ki_j_lt])
  have i_lt_cs: \<open>i < length cs\<close>
    using assms(1) assms(4) by simp
  have comp: \<open>invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen local_ntt ! i mod MLKEM_Q =
    2 * cs ! i mod MLKEM_Q\<close>
  proof -
    have \<open>invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen
           (ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs) ! i mod MLKEM_Q =
      (if i \<in> {j * (2 * blen)..<j * (2 * blen) + blen} \<or>
          i \<in> {j * (2 * blen) + blen..<j * (2 * blen) + blen + blen}
       then 2 * cs ! i mod MLKEM_Q
       else cs ! i mod MLKEM_Q)\<close>
      by (rule inner_loop_composition_ntt_invntt[OF assms(1) off_bound le_refl
            zeta_cancel zf_mod zi_mod i_lt_cs])
    moreover have \<open>i \<in> {j * (2 * blen)..<j * (2 * blen) + blen} \<or>
          i \<in> {j * (2 * blen) + blen..<j * (2 * blen) + blen + blen}\<close>
      using j_lo j_hi_aux by auto
    ultimately show ?thesis
      unfolding local_ntt_def by simp
  qed
  have \<open>invntt_layer_int l (ntt_layer_int l cs) ! i mod MLKEM_Q =
    invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen local_ntt ! i mod MLKEM_Q\<close>
    unfolding ntt_cs_def[symmetric] using invntt_decomp cong_step by simp
  also have \<open>\<dots> = 2 * cs ! i mod MLKEM_Q\<close>
    by (rule comp)
  finally show ?thesis .
qed

subsection \<open>Tier 6 — Linearity\<close>

text \<open>NTT layers are linear mod Q: scaling inputs by a constant scales
  outputs by the same constant. Needed to commute the Montgomery
  prescaling past the NTT layers in one direction of the proof.\<close>

text \<open>Helper: fqmul distributes scaling mod Q.\<close>

lemma fqmul_int_linear_mod:
  shows \<open>fqmul_int (a * k) b mod MLKEM_Q = fqmul_int a b * k mod MLKEM_Q\<close>
proof -
  have lhs: \<open>fqmul_int (a * k) b * 2^16 mod MLKEM_Q = a * k * b mod MLKEM_Q\<close>
    by (rule fqmul_int_cong)
  have rhs: \<open>fqmul_int a b * 2^16 mod MLKEM_Q = a * b mod MLKEM_Q\<close>
    by (rule fqmul_int_cong)
  have eq16: \<open>fqmul_int (a * k) b * 2^16 mod MLKEM_Q = fqmul_int a b * k * 2^16 mod MLKEM_Q\<close>
  proof -
    have \<open>fqmul_int a b * 2^16 * k mod MLKEM_Q = a * b * k mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF rhs refl])
    thus ?thesis
      using lhs by (simp add: algebra_simps)
  qed
  have cop: \<open>coprime MLKEM_Q ((2::int)^16)\<close>
    by eval
  show ?thesis
    by (rule mult_mod_cancel_right[OF eq16 cop])
qed

lemma ntt_layer_int_linear_mod:
  assumes \<open>length cs = MLKEM_N\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>i < MLKEM_N\<close>
    shows \<open>ntt_layer_int l (List.map (\<lambda>c. c * k) cs) ! i mod MLKEM_Q =
             ntt_layer_int l cs ! i * k mod MLKEM_Q\<close>
proof -
  define nb where
    \<open>nb = (2::nat)^(l-1)\<close>
  define blen where
    \<open>blen = (2::nat)^(8-l)\<close>
  define scaled where
    \<open>scaled = List.map (\<lambda>c. c * k) cs\<close>
  define j where
    \<open>j = i div (2 * blen)\<close>
  have nb_blen: \<open>nb * (2 * blen) = MLKEM_N\<close>
    using ntt_nb_blen_eq[OF assms(2) assms(3)] unfolding nb_def blen_def .
  have len_scaled: \<open>length scaled = MLKEM_N\<close>
    unfolding scaled_def using assms(1) by simp
  have i_lt: \<open>i < nb * (2 * blen)\<close>
    using assms(4) nb_blen by linarith
  have j_lt_nb: \<open>j < nb\<close>
    unfolding j_def using i_lt by (simp add: less_mult_imp_div_less)
  have sj_le_nb: \<open>Suc j \<le> nb\<close>
    using j_lt_nb by simp
  have j_lo: \<open>j * (2 * blen) \<le> i\<close>
    unfolding j_def by simp
  have j_hi_aux: \<open>i < j * (2 * blen) + 2 * blen\<close>
  proof -
    have blen_pos: \<open>(0::nat) < 2 * blen\<close>
      by (simp add: blen_def)
    have \<open>i mod (2 * blen) < 2 * blen\<close>
      using blen_pos by simp
    have \<open>i div (2 * blen) * (2 * blen) + i mod (2 * blen) = i\<close>
      by (rule div_mult_mod_eq)
    thus ?thesis unfolding j_def using \<open>i mod (2 * blen) < 2 * blen\<close>
      by linarith
  qed
  hence j_hi: \<open>i < Suc j * (2 * blen)\<close>
    by simp
  have block_len_cs: \<open>j * (2 * blen) + 2 * blen \<le> length cs\<close>
  proof -
    have \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
      by (rule mult_le_mono1[OF sj_le_nb])
    thus ?thesis
      using nb_blen assms(1) by simp
  qed
  have block_len_scaled: \<open>j * (2 * blen) + 2 * blen \<le> length scaled\<close>
    using block_len_cs len_scaled assms(1) by simp
  \<comment> \<open>Decompose layer to inner loop for block j\<close>
  have decomp_scaled: \<open>ntt_layer_int l scaled ! i =
    ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen scaled ! i\<close>
  proof -
    have \<open>snd (ntt_middle_loop_int nb blen nb nb scaled) ! i =
      ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen scaled ! i\<close>
      by (rule ntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen len_scaled)
    thus ?thesis
      unfolding ntt_layer_int_def nb_def blen_def .
  qed
  have decomp_cs: \<open>ntt_layer_int l cs ! i =
    ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs ! i\<close>
  proof -
    have \<open>snd (ntt_middle_loop_int nb blen nb nb cs) ! i =
      ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs ! i\<close>
      by (rule ntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen assms(1))
    thus ?thesis
      unfolding ntt_layer_int_def nb_def blen_def .
  qed
  show ?thesis
  proof (cases \<open>i < j * (2 * blen) + blen\<close>)
    case True
    define m where
      \<open>m = i - j * (2 * blen)\<close>
    have im: \<open>i = j * (2 * blen) + m\<close> and mb: \<open>m < blen\<close>
      using j_lo True by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < length cs\<close>
      using block_len_cs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < length cs\<close>
      using block_len_cs mb by linarith
    have scaled_lo: \<open>scaled ! (j * (2 * blen) + m) = cs ! (j * (2 * blen) + m) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_lo])
    have scaled_hi: \<open>scaled ! (j * (2 * blen) + m + blen) = cs ! (j * (2 * blen) + m + blen) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_hi])
    have val_scaled: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen scaled ! i =
      cs ! (j * (2 * blen) + m) * k + fqmul_int (cs ! (j * (2 * blen) + m + blen) * k) (zetas_int ! (nb + j))\<close>
      unfolding im using ntt_inner_loop_int_low_val[OF mb le_refl block_len_scaled]
        scaled_lo scaled_hi by simp
    have val_cs: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs ! i =
      cs ! (j * (2 * blen) + m) + fqmul_int (cs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))\<close>
      unfolding im by (rule ntt_inner_loop_int_low_val[OF mb le_refl block_len_cs])
    have \<open>ntt_layer_int l scaled ! i mod MLKEM_Q =
      (cs ! (j * (2 * blen) + m) * k +
       fqmul_int (cs ! (j * (2 * blen) + m + blen) * k) (zetas_int ! (nb + j))) mod MLKEM_Q\<close>
      using decomp_scaled val_scaled by simp
    also have \<open>\<dots> = (cs ! (j * (2 * blen) + m) * k +
       fqmul_int (cs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) * k) mod MLKEM_Q\<close>
      by (rule mod_add_cong[OF refl fqmul_int_linear_mod])
    also have \<open>\<dots> = (cs ! (j * (2 * blen) + m) +
       fqmul_int (cs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))) * k mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = ntt_layer_int l cs ! i * k mod MLKEM_Q\<close>
      using decomp_cs val_cs by simp
    finally show ?thesis
      unfolding scaled_def .
  next
    case False
    hence i_ge: \<open>j * (2 * blen) + blen \<le> i\<close>
      by simp
    define m where
      \<open>m = i - j * (2 * blen) - blen\<close>
    have im: \<open>i = j * (2 * blen) + m + blen\<close> and mb: \<open>m < blen\<close>
      using j_lo i_ge j_hi_aux by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < length cs\<close>
      using block_len_cs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < length cs\<close>
      using block_len_cs mb by linarith
    have scaled_lo: \<open>scaled ! (j * (2 * blen) + m) = cs ! (j * (2 * blen) + m) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_lo])
    have scaled_hi: \<open>scaled ! (j * (2 * blen) + m + blen) = cs ! (j * (2 * blen) + m + blen) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_hi])
    have val_scaled: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen scaled ! i =
      cs ! (j * (2 * blen) + m) * k - fqmul_int (cs ! (j * (2 * blen) + m + blen) * k) (zetas_int ! (nb + j))\<close>
      unfolding im using ntt_inner_loop_int_high_val[OF mb le_refl block_len_scaled]
        scaled_lo scaled_hi by simp
    have val_cs: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen cs ! i =
      cs ! (j * (2 * blen) + m) - fqmul_int (cs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))\<close>
      unfolding im by (rule ntt_inner_loop_int_high_val[OF mb le_refl block_len_cs])
    have \<open>ntt_layer_int l scaled ! i mod MLKEM_Q =
      (cs ! (j * (2 * blen) + m) * k -
       fqmul_int (cs ! (j * (2 * blen) + m + blen) * k) (zetas_int ! (nb + j))) mod MLKEM_Q\<close>
      using decomp_scaled val_scaled by simp
    also have \<open>\<dots> = (cs ! (j * (2 * blen) + m) * k -
       fqmul_int (cs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) * k) mod MLKEM_Q\<close>
      by (rule mod_diff_cong[OF refl fqmul_int_linear_mod])
    also have \<open>\<dots> = (cs ! (j * (2 * blen) + m) -
       fqmul_int (cs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))) * k mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = ntt_layer_int l cs ! i * k mod MLKEM_Q\<close>
      using decomp_cs val_cs by simp
    finally show ?thesis
      unfolding scaled_def .
  qed
qed

lemma invntt_layer_int_linear_mod:
  assumes \<open>length cs = MLKEM_N\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>i < MLKEM_N\<close>
  shows \<open>invntt_layer_int l (List.map (\<lambda>c. c * k) cs) ! i mod MLKEM_Q =
           invntt_layer_int l cs ! i * k mod MLKEM_Q\<close>
proof -
  define nb where
    \<open>nb = (2::nat)^(l-1)\<close>
  define blen where
    \<open>blen = (2::nat)^(8-l)\<close>
  define scaled where
    \<open>scaled = List.map (\<lambda>c. c * k) cs\<close>
  define j where
    \<open>j = i div (2 * blen)\<close>
  have nb_blen: \<open>nb * (2 * blen) = MLKEM_N\<close>
    using ntt_nb_blen_eq[OF assms(2) assms(3)] unfolding nb_def blen_def .
  have len_scaled: \<open>length scaled = MLKEM_N\<close>
    unfolding scaled_def using assms(1) by simp
  have i_lt: \<open>i < nb * (2 * blen)\<close>
    using assms(4) nb_blen by linarith
  have j_lt_nb: \<open>j < nb\<close>
    unfolding j_def using i_lt by (simp add: less_mult_imp_div_less)
  have sj_le_nb: \<open>Suc j \<le> nb\<close>
    using j_lt_nb by simp
  have j_lo: \<open>j * (2 * blen) \<le> i\<close>
    unfolding j_def by simp
  have j_hi_aux: \<open>i < j * (2 * blen) + 2 * blen\<close>
  proof -
    have blen_pos: \<open>(0::nat) < 2 * blen\<close>
      by (simp add: blen_def)
    have \<open>i mod (2 * blen) < 2 * blen\<close>
      using blen_pos by simp
    have \<open>i div (2 * blen) * (2 * blen) + i mod (2 * blen) = i\<close>
      by (rule div_mult_mod_eq)
    thus ?thesis
      unfolding j_def using \<open>i mod (2 * blen) < 2 * blen\<close> by linarith
  qed
  hence j_hi: \<open>i < Suc j * (2 * blen)\<close>
    by simp
  have block_len_cs: \<open>j * (2 * blen) + 2 * blen \<le> length cs\<close>
  proof -
    have \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
      by (rule mult_le_mono1[OF sj_le_nb])
    thus ?thesis
      using nb_blen assms(1) by simp
  qed
  have block_len_scaled: \<open>j * (2 * blen) + 2 * blen \<le> length scaled\<close>
    using block_len_cs len_scaled assms(1) by simp
  \<comment> \<open>Decompose layer to inner loop for block j\<close>
  have decomp_scaled: \<open>invntt_layer_int l scaled ! i =
    invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen scaled ! i\<close>
  proof -
    have \<open>snd (invntt_middle_loop_int (2^l - 1) blen nb nb scaled) ! i =
      invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen scaled ! i\<close>
      by (rule invntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen len_scaled)
    thus ?thesis
      unfolding invntt_layer_int_def nb_def blen_def .
  qed
  have decomp_cs: \<open>invntt_layer_int l cs ! i =
    invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen cs ! i\<close>
  proof -
    have \<open>snd (invntt_middle_loop_int (2^l - 1) blen nb nb cs) ! i =
      invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen cs ! i\<close>
      by (rule invntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen assms(1))
    thus ?thesis
      unfolding invntt_layer_int_def nb_def blen_def .
  qed
  show ?thesis
  proof (cases \<open>i < j * (2 * blen) + blen\<close>)
    case True
    define m where
      \<open>m = i - j * (2 * blen)\<close>
    have im: \<open>i = j * (2 * blen) + m\<close> and mb: \<open>m < blen\<close>
      using j_lo True by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < length cs\<close>
      using block_len_cs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < length cs\<close>
      using block_len_cs mb by linarith
    have scaled_lo: \<open>scaled ! (j * (2 * blen) + m) = cs ! (j * (2 * blen) + m) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_lo])
    have scaled_hi: \<open>scaled ! (j * (2 * blen) + m + blen) = cs ! (j * (2 * blen) + m + blen) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_hi])
    have val_scaled: \<open>invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen scaled ! i =
          barrett_reduce_int (cs ! (j * (2 * blen) + m) * k + cs ! (j * (2 * blen) + m + blen) * k)\<close>
      unfolding im using invntt_inner_loop_int_low_val[OF mb le_refl block_len_scaled]
        scaled_lo scaled_hi by simp
    have val_cs: \<open>invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen cs ! i =
          barrett_reduce_int (cs ! (j * (2 * blen) + m) + cs ! (j * (2 * blen) + m + blen))\<close>
      unfolding im by (rule invntt_inner_loop_int_low_val[OF mb le_refl block_len_cs])
    have factor: \<open>cs ! (j * (2 * blen) + m) * k + cs ! (j * (2 * blen) + m + blen) * k =
      (cs ! (j * (2 * blen) + m) + cs ! (j * (2 * blen) + m + blen)) * k\<close>
      by (simp add: algebra_simps)
    have \<open>invntt_layer_int l scaled ! i mod MLKEM_Q =
          barrett_reduce_int ((cs ! (j * (2 * blen) + m) + cs ! (j * (2 * blen) + m + blen)) * k) mod MLKEM_Q\<close>
      using decomp_scaled val_scaled factor by simp
    also have \<open>\<dots> = (cs ! (j * (2 * blen) + m) + cs ! (j * (2 * blen) + m + blen)) * k mod MLKEM_Q\<close>
      by (rule barrett_reduce_mod)
    also have \<open>\<dots> = barrett_reduce_int (cs ! (j * (2 * blen) + m) + cs ! (j * (2 * blen) + m + blen)) * k mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF barrett_reduce_mod[symmetric] refl])
    also have \<open>\<dots> = invntt_layer_int l cs ! i * k mod MLKEM_Q\<close>
      using decomp_cs val_cs by simp
    finally show ?thesis
      unfolding scaled_def .
  next
    case False
    hence i_ge: \<open>j * (2 * blen) + blen \<le> i\<close>
      by simp
    define m where
      \<open>m = i - j * (2 * blen) - blen\<close>
    have im: \<open>i = j * (2 * blen) + m + blen\<close> and mb: \<open>m < blen\<close>
      using j_lo i_ge j_hi_aux by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < length cs\<close>
      using block_len_cs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < length cs\<close>
      using block_len_cs mb by linarith
    have scaled_lo: \<open>scaled ! (j * (2 * blen) + m) = cs ! (j * (2 * blen) + m) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_lo])
    have scaled_hi: \<open>scaled ! (j * (2 * blen) + m + blen) = cs ! (j * (2 * blen) + m + blen) * k\<close>
      unfolding scaled_def by (simp add: nth_map[OF idx_hi])
    have val_scaled: \<open>invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen scaled ! i =
          fqmul_int (cs ! (j * (2 * blen) + m + blen) * k - cs ! (j * (2 * blen) + m) * k) (zetas_int ! (2^l - 1 - j))\<close>
      unfolding im using invntt_inner_loop_int_high_val[OF mb le_refl block_len_scaled]
        scaled_lo scaled_hi by simp
    have val_cs: \<open>invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen cs ! i =
          fqmul_int (cs ! (j * (2 * blen) + m + blen) - cs ! (j * (2 * blen) + m)) (zetas_int ! (2^l - 1 - j))\<close>
      unfolding im by (rule invntt_inner_loop_int_high_val[OF mb le_refl block_len_cs])
    have factor: \<open>cs ! (j * (2 * blen) + m + blen) * k - cs ! (j * (2 * blen) + m) * k =
          (cs ! (j * (2 * blen) + m + blen) - cs ! (j * (2 * blen) + m)) * k\<close>
      by (simp add: algebra_simps)
    have \<open>invntt_layer_int l scaled ! i mod MLKEM_Q =
          fqmul_int ((cs ! (j * (2 * blen) + m + blen) - cs ! (j * (2 * blen) + m)) * k)
            (zetas_int ! (2^l - 1 - j)) mod MLKEM_Q\<close>
      using decomp_scaled val_scaled factor by simp
    also have \<open>\<dots> = fqmul_int (cs ! (j * (2 * blen) + m + blen) - cs ! (j * (2 * blen) + m))
            (zetas_int ! (2^l - 1 - j)) * k mod MLKEM_Q\<close>
      by (rule fqmul_int_linear_mod)
    also have \<open>\<dots> = invntt_layer_int l cs ! i * k mod MLKEM_Q\<close>
      using decomp_cs val_cs by simp
    finally show ?thesis
      unfolding scaled_def .
  qed
qed

subsection \<open>Tier 7 — Full Transform Composition\<close>

text \<open>Helper: @{const fqmul_int} preserves mod-Q congruence in the first argument.\<close>

lemma fqmul_int_mod_cong:
  assumes \<open>a mod MLKEM_Q = b mod MLKEM_Q\<close>
    shows \<open>fqmul_int a z mod MLKEM_Q = fqmul_int b z mod MLKEM_Q\<close>
proof -
  have la: \<open>fqmul_int a z * 2^16 mod MLKEM_Q = a * z mod MLKEM_Q\<close>
    by (rule fqmul_int_cong)
  have lb: \<open>fqmul_int b z * 2^16 mod MLKEM_Q = b * z mod MLKEM_Q\<close>
    by (rule fqmul_int_cong)
  have \<open>a * z mod MLKEM_Q = b * z mod MLKEM_Q\<close>
    using assms by (rule mod_mult_cong[OF _ refl])
  hence \<open>fqmul_int a z * 2^16 mod MLKEM_Q = fqmul_int b z * 2^16 mod MLKEM_Q\<close>
    using la lb by simp
  thus ?thesis
    by (rule mult_mod_cancel_right) eval
qed

text \<open>Combined congruence + linearity for a single NTT layer.\<close>

lemma ntt_layer_int_linear_cong:
  assumes cong: \<open>\<forall>j < MLKEM_N. xs ! j mod MLKEM_Q = ys ! j * k mod MLKEM_Q\<close>
      and len_xs: \<open>length xs = MLKEM_N\<close>
      and len_ys: \<open>length ys = MLKEM_N\<close>
      and l_ge: \<open>1 \<le> l\<close>
      and l_le: \<open>l \<le> 7\<close>
      and i_lt: \<open>i < MLKEM_N\<close>
    shows \<open>ntt_layer_int l xs ! i mod MLKEM_Q =
             ntt_layer_int l ys ! i * k mod MLKEM_Q\<close>
proof -
  define nb where \<open>nb = (2::nat)^(l-1)\<close>
  define blen where \<open>blen = (2::nat)^(8-l)\<close>
  define j where \<open>j = i div (2 * blen)\<close>
  have nb_blen: \<open>nb * (2 * blen) = MLKEM_N\<close>
    using ntt_nb_blen_eq[OF l_ge l_le] unfolding nb_def blen_def .
  have i_lt2: \<open>i < nb * (2 * blen)\<close>
    using i_lt nb_blen by linarith
  have j_lt_nb: \<open>j < nb\<close>
    unfolding j_def using i_lt2 by (simp add: less_mult_imp_div_less)
  have sj_le_nb: \<open>Suc j \<le> nb\<close>
    using j_lt_nb by simp
  have j_lo: \<open>j * (2 * blen) \<le> i\<close>
    unfolding j_def by simp
  have j_hi_aux: \<open>i < j * (2 * blen) + 2 * blen\<close>
  proof -
    have \<open>(0::nat) < 2 * blen\<close> by (simp add: blen_def)
    have \<open>i mod (2 * blen) < 2 * blen\<close> using \<open>0 < 2 * blen\<close> by simp
    have \<open>i div (2 * blen) * (2 * blen) + i mod (2 * blen) = i\<close>
      by (rule div_mult_mod_eq)
    thus ?thesis unfolding j_def using \<open>i mod (2 * blen) < 2 * blen\<close>
      by linarith
  qed
  hence j_hi: \<open>i < Suc j * (2 * blen)\<close> by simp
  have block_len_xs: \<open>j * (2 * blen) + 2 * blen \<le> length xs\<close>
  proof -
    have \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
      by (rule mult_le_mono1[OF sj_le_nb])
    thus ?thesis using nb_blen len_xs by simp
  qed
  have block_len_ys: \<open>j * (2 * blen) + 2 * blen \<le> length ys\<close>
  proof -
    have \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
      by (rule mult_le_mono1[OF sj_le_nb])
    thus ?thesis using nb_blen len_ys by simp
  qed
  have decomp_xs: \<open>ntt_layer_int l xs ! i =
    ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen xs ! i\<close>
  proof -
    have \<open>snd (ntt_middle_loop_int nb blen nb nb xs) ! i =
      ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen xs ! i\<close>
      by (rule ntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen len_xs)
    thus ?thesis
      unfolding ntt_layer_int_def nb_def blen_def .
  qed
  have decomp_ys: \<open>ntt_layer_int l ys ! i =
    ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen ys ! i\<close>
  proof -
    have \<open>snd (ntt_middle_loop_int nb blen nb nb ys) ! i =
      ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen ys ! i\<close>
      by (rule ntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen len_ys)
    thus ?thesis
      unfolding ntt_layer_int_def nb_def blen_def .
  qed
  show ?thesis
  proof (cases \<open>i < j * (2 * blen) + blen\<close>)
    case True
    define m where \<open>m = i - j * (2 * blen)\<close>
    have im: \<open>i = j * (2 * blen) + m\<close> and mb: \<open>m < blen\<close>
      using j_lo True by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have cong_lo: \<open>xs ! (j * (2 * blen) + m) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m) * k mod MLKEM_Q\<close>
      using cong idx_lo by auto
    have cong_hi: \<open>xs ! (j * (2 * blen) + m + blen) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m + blen) * k mod MLKEM_Q\<close>
      using cong idx_hi by auto
    have fqmul_cong: \<open>fqmul_int (xs ! (j * (2 * blen) + m + blen))
                       (zetas_int ! (nb + j)) mod MLKEM_Q =
                      fqmul_int (ys ! (j * (2 * blen) + m + blen))
                       (zetas_int ! (nb + j)) * k mod MLKEM_Q\<close>
    proof -
      have \<open>fqmul_int (xs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) mod MLKEM_Q =
            fqmul_int (ys ! (j * (2 * blen) + m + blen) * k) (zetas_int ! (nb + j)) mod MLKEM_Q\<close>
        by (rule fqmul_int_mod_cong[OF cong_hi])
      also have \<open>\<dots> = fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) * k mod MLKEM_Q\<close>
        by (rule fqmul_int_linear_mod)
      finally show ?thesis .
    qed
    have val_xs: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen xs ! i =
      xs ! (j * (2 * blen) + m) +
        fqmul_int (xs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))\<close>
      unfolding im by (rule ntt_inner_loop_int_low_val[OF mb le_refl block_len_xs])
    have val_ys: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen ys ! i =
      ys ! (j * (2 * blen) + m) +
        fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))\<close>
      unfolding im by (rule ntt_inner_loop_int_low_val[OF mb le_refl block_len_ys])
    have \<open>ntt_layer_int l xs ! i mod MLKEM_Q =
      (xs ! (j * (2 * blen) + m) +
        fqmul_int (xs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))) mod MLKEM_Q\<close>
      using decomp_xs val_xs by simp
    also have \<open>\<dots> = (ys ! (j * (2 * blen) + m) * k +
        fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) * k) mod MLKEM_Q\<close>
      by (rule mod_add_cong[OF cong_lo fqmul_cong])
    also have \<open>\<dots> = (ys ! (j * (2 * blen) + m) +
        fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))) * k mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = ntt_layer_int l ys ! i * k mod MLKEM_Q\<close>
      using decomp_ys val_ys by simp
    finally show ?thesis .
  next
    case False
    hence i_ge: \<open>j * (2 * blen) + blen \<le> i\<close> by simp
    define m where \<open>m = i - j * (2 * blen) - blen\<close>
    have im: \<open>i = j * (2 * blen) + m + blen\<close> and mb: \<open>m < blen\<close>
      using j_lo i_ge j_hi_aux by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have cong_lo: \<open>xs ! (j * (2 * blen) + m) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m) * k mod MLKEM_Q\<close>
      using cong idx_lo by auto
    have cong_hi: \<open>xs ! (j * (2 * blen) + m + blen) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m + blen) * k mod MLKEM_Q\<close>
      using cong idx_hi by auto
    have fqmul_cong: \<open>fqmul_int (xs ! (j * (2 * blen) + m + blen))
                       (zetas_int ! (nb + j)) mod MLKEM_Q =
                      fqmul_int (ys ! (j * (2 * blen) + m + blen))
                       (zetas_int ! (nb + j)) * k mod MLKEM_Q\<close>
    proof -
      have \<open>fqmul_int (xs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) mod MLKEM_Q =
            fqmul_int (ys ! (j * (2 * blen) + m + blen) * k) (zetas_int ! (nb + j)) mod MLKEM_Q\<close>
        by (rule fqmul_int_mod_cong[OF cong_hi])
      also have \<open>\<dots> = fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) * k mod MLKEM_Q\<close>
        by (rule fqmul_int_linear_mod)
      finally show ?thesis .
    qed
    have val_xs: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen xs ! i =
      xs ! (j * (2 * blen) + m) -
        fqmul_int (xs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))\<close>
      unfolding im by (rule ntt_inner_loop_int_high_val[OF mb le_refl block_len_xs])
    have val_ys: \<open>ntt_inner_loop_int (zetas_int ! (nb + j)) (j * (2 * blen)) blen blen ys ! i =
      ys ! (j * (2 * blen) + m) -
        fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))\<close>
      unfolding im by (rule ntt_inner_loop_int_high_val[OF mb le_refl block_len_ys])
    have \<open>ntt_layer_int l xs ! i mod MLKEM_Q =
      (xs ! (j * (2 * blen) + m) -
        fqmul_int (xs ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))) mod MLKEM_Q\<close>
      using decomp_xs val_xs by simp
    also have \<open>\<dots> = (ys ! (j * (2 * blen) + m) * k -
        fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j)) * k) mod MLKEM_Q\<close>
      by (rule mod_diff_cong[OF cong_lo fqmul_cong])
    also have \<open>\<dots> = (ys ! (j * (2 * blen) + m) -
        fqmul_int (ys ! (j * (2 * blen) + m + blen)) (zetas_int ! (nb + j))) * k mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = ntt_layer_int l ys ! i * k mod MLKEM_Q\<close>
      using decomp_ys val_ys by simp
    finally show ?thesis .
  qed
qed

text \<open>Analogous combined congruence + linearity for a single inverse NTT layer.\<close>

lemma invntt_layer_int_linear_cong:
  assumes cong: \<open>\<forall>j < MLKEM_N. xs ! j mod MLKEM_Q = ys ! j * k mod MLKEM_Q\<close>
      and len_xs: \<open>length xs = MLKEM_N\<close>
      and len_ys: \<open>length ys = MLKEM_N\<close>
      and l_ge: \<open>1 \<le> l\<close>
      and l_le: \<open>l \<le> 7\<close>
      and i_lt: \<open>i < MLKEM_N\<close>
    shows \<open>invntt_layer_int l xs ! i mod MLKEM_Q =
             invntt_layer_int l ys ! i * k mod MLKEM_Q\<close>
proof -
  define nb where
    \<open>nb = (2::nat)^(l-1)\<close>
  define blen where
    \<open>blen = (2::nat)^(8-l)\<close>
  define j where
    \<open>j = i div (2 * blen)\<close>
  define ki where
    \<open>ki = (2::nat)^l - 1 - j\<close>
  have nb_blen: \<open>nb * (2 * blen) = MLKEM_N\<close>
    using ntt_nb_blen_eq[OF l_ge l_le] unfolding nb_def blen_def .
  have i_lt2: \<open>i < nb * (2 * blen)\<close>
    using i_lt nb_blen by linarith
  have j_lt_nb: \<open>j < nb\<close>
    unfolding j_def using i_lt2 by (simp add: less_mult_imp_div_less)
  have sj_le_nb: \<open>Suc j \<le> nb\<close>
    using j_lt_nb by simp
  have j_lo: \<open>j * (2 * blen) \<le> i\<close>
    unfolding j_def by simp
  have j_hi_aux: \<open>i < j * (2 * blen) + 2 * blen\<close>
  proof -
    have \<open>(0::nat) < 2 * blen\<close>
      by (simp add: blen_def)
    have \<open>i mod (2 * blen) < 2 * blen\<close> using \<open>0 < 2 * blen\<close>
      by simp
    have \<open>i div (2 * blen) * (2 * blen) + i mod (2 * blen) = i\<close>
      by (rule div_mult_mod_eq)
    thus ?thesis unfolding j_def using \<open>i mod (2 * blen) < 2 * blen\<close>
      by linarith
  qed
  hence j_hi: \<open>i < Suc j * (2 * blen)\<close>
    by simp
  have block_len_xs: \<open>j * (2 * blen) + 2 * blen \<le> length xs\<close>
  proof -
    have \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
      by (rule mult_le_mono1[OF sj_le_nb])
    thus ?thesis
      using nb_blen len_xs by simp
  qed
  have block_len_ys: \<open>j * (2 * blen) + 2 * blen \<le> length ys\<close>
  proof -
    have \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
      by (rule mult_le_mono1[OF sj_le_nb])
    thus ?thesis
      using nb_blen len_ys by simp
  qed
  have two_nb: \<open>2 * nb = 2^l\<close>
  proof -
    have \<open>(2::nat) * 2^(l-1) = 2^Suc (l-1)\<close>
      by simp
    also have \<open>Suc (l-1) = l\<close>
      using l_ge by simp
    finally show ?thesis
      by (simp add: nb_def)
  qed
  have ki_eq: \<open>ki = 2^l - 1 - j\<close>
    unfolding ki_def by simp
  have decomp_xs: \<open>invntt_layer_int l xs ! i =
    invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen xs ! i\<close>
  proof -
    have \<open>snd (invntt_middle_loop_int (2^l - 1) blen nb nb xs) ! i =
      invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen xs ! i\<close>
      by (rule invntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen len_xs)
    thus ?thesis
      unfolding invntt_layer_int_def nb_def blen_def ki_eq using two_nb nb_def by simp
  qed
  have decomp_ys: \<open>invntt_layer_int l ys ! i =
    invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen ys ! i\<close>
  proof -
    have \<open>snd (invntt_middle_loop_int (2^l - 1) blen nb nb ys) ! i =
      invntt_inner_loop_int (zetas_int ! (2^l - 1 - j)) (j * (2 * blen)) blen blen ys ! i\<close>
      by (rule invntt_middle_loop_at_block[OF j_lt_nb _ j_lo j_hi])
         (simp add: nb_blen len_ys)
    thus ?thesis
      unfolding invntt_layer_int_def nb_def blen_def ki_eq using two_nb nb_def by simp
  qed
  show ?thesis
  proof (cases \<open>i < j * (2 * blen) + blen\<close>)
    case True
    define m where
      \<open>m = i - j * (2 * blen)\<close>
    have im: \<open>i = j * (2 * blen) + m\<close> and mb: \<open>m < blen\<close>
      using j_lo True by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have cong_lo: \<open>xs ! (j * (2 * blen) + m) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m) * k mod MLKEM_Q\<close>
      using cong idx_lo by auto
    have cong_hi: \<open>xs ! (j * (2 * blen) + m + blen) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m + blen) * k mod MLKEM_Q\<close>
      using cong idx_hi by auto
    \<comment> \<open>Low position: barrett_reduce(xs[lo] + xs[hi])\<close>
    have val_xs: \<open>invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen xs ! i =
            barrett_reduce_int (xs ! (j * (2 * blen) + m) + xs ! (j * (2 * blen) + m + blen))\<close>
      unfolding im by (rule invntt_inner_loop_int_low_val[OF mb le_refl block_len_xs])
    have val_ys: \<open>invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen ys ! i =
            barrett_reduce_int (ys ! (j * (2 * blen) + m) + ys ! (j * (2 * blen) + m + blen))\<close>
      unfolding im by (rule invntt_inner_loop_int_low_val[OF mb le_refl block_len_ys])
    have \<open>invntt_layer_int l xs ! i mod MLKEM_Q =
            barrett_reduce_int (xs ! (j * (2 * blen) + m) + xs ! (j * (2 * blen) + m + blen)) mod MLKEM_Q\<close>
      using decomp_xs val_xs by simp
    also have \<open>\<dots> = (xs ! (j * (2 * blen) + m) + xs ! (j * (2 * blen) + m + blen)) mod MLKEM_Q\<close>
      by (rule barrett_reduce_mod)
    also have \<open>\<dots> = (ys ! (j * (2 * blen) + m) * k + ys ! (j * (2 * blen) + m + blen) * k) mod MLKEM_Q\<close>
      by (rule mod_add_cong[OF cong_lo cong_hi])
    also have \<open>\<dots> = (ys ! (j * (2 * blen) + m) + ys ! (j * (2 * blen) + m + blen)) * k mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    also have \<open>\<dots> = barrett_reduce_int (ys ! (j * (2 * blen) + m) + ys ! (j * (2 * blen) + m + blen)) * k mod MLKEM_Q\<close>
    proof -
      have \<open>(ys ! (j * (2 * blen) + m) + ys ! (j * (2 * blen) + m + blen)) mod MLKEM_Q =
            barrett_reduce_int (ys ! (j * (2 * blen) + m) + ys ! (j * (2 * blen) + m + blen)) mod MLKEM_Q\<close>
        by (rule barrett_reduce_mod[symmetric])
      thus ?thesis
        by (rule mod_mult_cong[OF _ refl])
    qed
    also have \<open>\<dots> = invntt_layer_int l ys ! i * k mod MLKEM_Q\<close>
      using decomp_ys val_ys by simp
    finally show ?thesis .
  next
    case False
    hence i_ge: \<open>j * (2 * blen) + blen \<le> i\<close>
      by simp
    define m where
      \<open>m = i - j * (2 * blen) - blen\<close>
    have im: \<open>i = j * (2 * blen) + m + blen\<close> and mb: \<open>m < blen\<close>
      using j_lo i_ge j_hi_aux by (auto simp: m_def)
    have idx_lo: \<open>j * (2 * blen) + m < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have idx_hi: \<open>j * (2 * blen) + m + blen < MLKEM_N\<close>
      using block_len_xs len_xs mb by linarith
    have cong_lo: \<open>xs ! (j * (2 * blen) + m) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m) * k mod MLKEM_Q\<close>
      using cong idx_lo by auto
    have cong_hi: \<open>xs ! (j * (2 * blen) + m + blen) mod MLKEM_Q =
                   ys ! (j * (2 * blen) + m + blen) * k mod MLKEM_Q\<close>
      using cong idx_hi by auto
    \<comment> \<open>High position: fqmul(xs[hi] - xs[lo], zeta)\<close>
    have fqmul_cong: \<open>fqmul_int (xs ! (j * (2 * blen) + m + blen) - xs ! (j * (2 * blen) + m))
                       (zetas_int ! ki) mod MLKEM_Q =
                      fqmul_int (ys ! (j * (2 * blen) + m + blen) - ys ! (j * (2 * blen) + m))
                       (zetas_int ! ki) * k mod MLKEM_Q\<close>
    proof -
      have diff_cong: \<open>(xs ! (j * (2 * blen) + m + blen) - xs ! (j * (2 * blen) + m)) mod MLKEM_Q =
        (ys ! (j * (2 * blen) + m + blen) - ys ! (j * (2 * blen) + m)) * k mod MLKEM_Q\<close>
      proof -
        have \<open>(xs ! (j * (2 * blen) + m + blen) - xs ! (j * (2 * blen) + m)) mod MLKEM_Q =
              (ys ! (j * (2 * blen) + m + blen) * k - ys ! (j * (2 * blen) + m) * k) mod MLKEM_Q\<close>
          by (rule mod_diff_cong[OF cong_hi cong_lo])
        also have \<open>\<dots> = (ys ! (j * (2 * blen) + m + blen) - ys ! (j * (2 * blen) + m)) * k mod MLKEM_Q\<close>
          by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      have \<open>fqmul_int (xs ! (j * (2 * blen) + m + blen) - xs ! (j * (2 * blen) + m))
                       (zetas_int ! ki) mod MLKEM_Q =
            fqmul_int ((ys ! (j * (2 * blen) + m + blen) - ys ! (j * (2 * blen) + m)) * k)
                       (zetas_int ! ki) mod MLKEM_Q\<close>
        by (rule fqmul_int_mod_cong[OF diff_cong])
      also have \<open>\<dots> = fqmul_int (ys ! (j * (2 * blen) + m + blen) - ys ! (j * (2 * blen) + m))
                       (zetas_int ! ki) * k mod MLKEM_Q\<close>
        by (rule fqmul_int_linear_mod)
      finally show ?thesis .
    qed
    have val_xs: \<open>invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen xs ! i =
      fqmul_int (xs ! (j * (2 * blen) + m + blen) - xs ! (j * (2 * blen) + m)) (zetas_int ! ki)\<close>
      unfolding im by (rule invntt_inner_loop_int_high_val[OF mb le_refl block_len_xs])
    have val_ys: \<open>invntt_inner_loop_int (zetas_int ! ki) (j * (2 * blen)) blen blen ys ! i =
      fqmul_int (ys ! (j * (2 * blen) + m + blen) - ys ! (j * (2 * blen) + m)) (zetas_int ! ki)\<close>
      unfolding im by (rule invntt_inner_loop_int_high_val[OF mb le_refl block_len_ys])
    have \<open>invntt_layer_int l xs ! i mod MLKEM_Q =
      fqmul_int (xs ! (j * (2 * blen) + m + blen) - xs ! (j * (2 * blen) + m)) (zetas_int ! ki) mod MLKEM_Q\<close>
      using decomp_xs val_xs by simp
    also have \<open>\<dots> = fqmul_int (ys ! (j * (2 * blen) + m + blen) - ys ! (j * (2 * blen) + m)) (zetas_int ! ki) * k mod MLKEM_Q\<close>
      by (rule fqmul_cong)
    also have \<open>\<dots> = invntt_layer_int l ys ! i * k mod MLKEM_Q\<close>
      using decomp_ys val_ys by simp
    finally show ?thesis .
  qed
qed

text \<open>Prescaling identity: 7 layer pairs contribute @{text "2^7 = 128"},
  and @{text "fqmul(x, 1441)"} contributes @{text "1441 / 2^{16} \<equiv> 512 (mod Q)"},
  giving @{text "128 \<times> 512 = 2^{16}"}.\<close>

lemma prescale_factor:
  shows \<open>(128::int) * fqmul_int x 1441 mod MLKEM_Q = x * 2^16 mod MLKEM_Q\<close>
proof -
  have s1: \<open>fqmul_int x 1441 * 2^16 mod MLKEM_Q = x * 1441 mod MLKEM_Q\<close>
    by (rule fqmul_int_cong)
  have s2: \<open>128 * (fqmul_int x 1441 * 2^16) mod MLKEM_Q = 128 * (x * 1441) mod MLKEM_Q\<close>
    by (rule mod_mult_cong[OF refl s1])
  have s3: \<open>(128 * 1441 :: int) mod MLKEM_Q = 2^32 mod MLKEM_Q\<close>
    by eval
  have s4: \<open>x * (128 * 1441) mod MLKEM_Q = x * 2^32 mod MLKEM_Q\<close>
    by (rule mod_mult_cong[OF refl s3])
  have pow: \<open>(2::int)^32 = 2^16 * 2^16\<close> 
    by eval
  have \<open>128 * fqmul_int x 1441 * 2^16 mod MLKEM_Q = x * 2^16 * 2^16 mod MLKEM_Q\<close>
    using s2 s4 pow by (simp add: algebra_simps)
  thus ?thesis
    by (rule mult_mod_cancel_right) eval
qed

lemma invntt_outer_loop_step:
  shows \<open>invntt_outer_loop_int (Suc n) cs = invntt_outer_loop_int n (invntt_layer_int (Suc n) cs)\<close>
by (simp add: case_prod_beta Let_def invntt_layer_int_def)

text \<open>The NTT outer loop preserves mod-Q linear congruence: if every coefficient
  of @{term xs} agrees mod Q with the corresponding coefficient of @{term ys}
  scaled by @{term k}, then the same holds after applying any suffix of NTT layers.\<close>

lemma ntt_outer_loop_linear_cong:
  assumes cong: \<open>\<forall>j < MLKEM_N. xs ! j mod MLKEM_Q = ys ! j * k mod MLKEM_Q\<close>
      and len_xs: \<open>length xs = MLKEM_N\<close>
      and len_ys: \<open>length ys = MLKEM_N\<close>
      and i_lt: \<open>i < MLKEM_N\<close>
      and n_ge: \<open>1 \<le> n\<close>
      and n_le: \<open>n \<le> 7\<close>
    shows \<open>ntt_outer_loop_int (2^(7-n)) n xs ! i mod MLKEM_Q =
           ntt_outer_loop_int (2^(7-n)) n ys ! i * k mod MLKEM_Q\<close>
using assms proof (induction n arbitrary: xs ys)
  case 0
  then show ?case by simp
next
  case (Suc m)
  define l where
    \<open>l = (8 - Suc m :: nat)\<close>
  have l_ge: \<open>1 \<le> l\<close> and l_le: \<open>l \<le> 7\<close>
    using Suc.prems unfolding l_def by auto
  have k_eq: \<open>2^(7 - Suc m) = (2::nat)^(l - 1)\<close>
    unfolding l_def using Suc.prems by auto
  have k_eq2: \<open>2^(7 - m) = (2::nat)^l\<close>
    unfolding l_def using Suc.prems by auto
  have m_eq: \<open>Suc m = 8 - l\<close>
    unfolding l_def using Suc.prems by auto
  have m_eq2: \<open>m = 7 - l\<close>
    unfolding l_def using Suc.prems by auto
  \<comment> \<open>Peel layer l from NTT outer loop\<close>
  have xs_step: \<open>ntt_outer_loop_int (2^(l-1)) (8-l) xs =
          ntt_outer_loop_int (2^l) (7-l) (ntt_layer_int l xs)\<close>
    by (rule ntt_outer_loop_step_layer[OF l_ge l_le])
  have ys_step: \<open>ntt_outer_loop_int (2^(l-1)) (8-l) ys =
          ntt_outer_loop_int (2^l) (7-l) (ntt_layer_int l ys)\<close>
    by (rule ntt_outer_loop_step_layer[OF l_ge l_le])
  \<comment> \<open>Layer l preserves the congruence\<close>
  have layer_cong: \<open>\<forall>j < MLKEM_N. ntt_layer_int l xs ! j mod MLKEM_Q =
          ntt_layer_int l ys ! j * k mod MLKEM_Q\<close>
    using ntt_layer_int_linear_cong[OF Suc.prems(1) Suc.prems(2) Suc.prems(3) l_ge l_le] by auto
  have len_lx: \<open>length (ntt_layer_int l xs) = MLKEM_N\<close>
    using Suc.prems(2) ntt_layer_int_length by auto
  have len_ly: \<open>length (ntt_layer_int l ys) = MLKEM_N\<close>
    using Suc.prems(3) ntt_layer_int_length by auto
  show ?case
  proof (cases \<open>m = 0\<close>)
    case True
    \<comment> \<open>Base: Suc m = 1, layer 7, loop terminates after one step\<close>
    have \<open>l = 7\<close>
      using True l_def Suc.prems by auto
    hence \<open>ntt_outer_loop_int (2^(7 - Suc m)) (Suc m) xs =
           ntt_layer_int 7 xs\<close>
      using xs_step k_eq m_eq by simp
    moreover have \<open>ntt_outer_loop_int (2^(7 - Suc m)) (Suc m) ys =
           ntt_layer_int 7 ys\<close>
      using ys_step k_eq m_eq \<open>l = 7\<close> by simp
    moreover have \<open>ntt_layer_int 7 xs ! i mod MLKEM_Q =
           ntt_layer_int 7 ys ! i * k mod MLKEM_Q\<close>
      using layer_cong \<open>l = 7\<close> Suc.prems(4) by auto
    ultimately show ?thesis
      by simp
  next
    case False
    hence m_ge: \<open>1 \<le> m\<close>
      by simp
    have m_le: \<open>m \<le> 7\<close>
      using Suc.prems by simp
    \<comment> \<open>Apply IH to the remaining layers\<close>
    have IH: \<open>ntt_outer_loop_int (2^(7-m)) m (ntt_layer_int l xs) ! i mod MLKEM_Q =
              ntt_outer_loop_int (2^(7-m)) m (ntt_layer_int l ys) ! i * k mod MLKEM_Q\<close>
      by (rule Suc.IH[OF layer_cong len_lx len_ly Suc.prems(4) m_ge m_le])
    show ?thesis
      using xs_step ys_step IH k_eq k_eq2 m_eq m_eq2 by simp
  qed
qed

text \<open>Analogous linear congruence for the inverse NTT outer loop.\<close>

lemma invntt_outer_loop_linear_cong:
  assumes cong: \<open>\<forall>j < MLKEM_N. xs ! j mod MLKEM_Q = ys ! j * k mod MLKEM_Q\<close>
      and len_xs: \<open>length xs = MLKEM_N\<close>
      and len_ys: \<open>length ys = MLKEM_N\<close>
      and i_lt: \<open>i < MLKEM_N\<close>
      and n_le: \<open>n \<le> 7\<close>
    shows \<open>invntt_outer_loop_int n xs ! i mod MLKEM_Q =
           invntt_outer_loop_int n ys ! i * k mod MLKEM_Q\<close>
using assms proof (induction n arbitrary: xs ys)
  case 0
  then show ?case by simp
next
  case (Suc m)
  define l where
    \<open>l = Suc m\<close>
  have l_ge: \<open>1 \<le> l\<close> and l_le: \<open>l \<le> 7\<close>
    using Suc.prems unfolding l_def by auto
  have layer_cong: \<open>\<forall>j < MLKEM_N. invntt_layer_int l xs ! j mod MLKEM_Q =
          invntt_layer_int l ys ! j * k mod MLKEM_Q\<close>
    using invntt_layer_int_linear_cong[OF Suc.prems(1) Suc.prems(2) Suc.prems(3) l_ge l_le] by auto
  have len_lx: \<open>length (invntt_layer_int l xs) = MLKEM_N\<close>
    using Suc.prems(2) invntt_layer_int_length by auto
  have len_ly: \<open>length (invntt_layer_int l ys) = MLKEM_N\<close>
    using Suc.prems(3) invntt_layer_int_length by auto
  have m_le: \<open>m \<le> 7\<close>
    using Suc.prems by simp
  have \<open>invntt_outer_loop_int (Suc m) xs = invntt_outer_loop_int m (invntt_layer_int l xs)\<close>
    unfolding l_def by (rule invntt_outer_loop_step)
  moreover have \<open>invntt_outer_loop_int (Suc m) ys = invntt_outer_loop_int m (invntt_layer_int l ys)\<close>
    unfolding l_def by (rule invntt_outer_loop_step)
  moreover have \<open>invntt_outer_loop_int m (invntt_layer_int l xs) ! i mod MLKEM_Q =
          invntt_outer_loop_int m (invntt_layer_int l ys) ! i * k mod MLKEM_Q\<close>
    by (rule Suc.IH[OF layer_cong len_lx len_ly Suc.prems(4) m_le])
  ultimately show ?case
    by simp
qed

text \<open>Full NTT/invNTT composition: 7 layer pairs each contribute factor 2.\<close>

lemma ntt_invntt_outer_compose:
  assumes len: \<open>length cs = MLKEM_N\<close>
      and i_lt: \<open>i < MLKEM_N\<close>
    shows \<open>ntt_outer_loop_int 1 7 (invntt_outer_loop_int 7 cs) ! i mod MLKEM_Q =
           (2::int)^7 * cs ! i mod MLKEM_Q\<close>
proof -
  \<comment> \<open>Unfold invNTT layers 7 down to 1\<close>
  define I7 where \<open>I7 = invntt_layer_int 7 cs\<close>
  define I6 where \<open>I6 = invntt_layer_int 6 I7\<close>
  define I5 where \<open>I5 = invntt_layer_int 5 I6\<close>
  define I4 where \<open>I4 = invntt_layer_int 4 I5\<close>
  define I3 where \<open>I3 = invntt_layer_int 3 I4\<close>
  define I2 where \<open>I2 = invntt_layer_int 2 I3\<close>
  define I1 where \<open>I1 = invntt_layer_int 1 I2\<close>
  have invntt_eq: \<open>invntt_outer_loop_int 7 cs = I1\<close>
    unfolding I1_def I2_def I3_def I4_def I5_def I6_def I7_def
    by (simp only: numeral_eq_Suc pred_numeral_simps Num.BitM.simps
                   One_nat_def invntt_outer_loop_step invntt_outer_loop_int.simps(1))
  \<comment> \<open>Length lemmas\<close>
  have [simp]: \<open>length I7 = MLKEM_N\<close> \<open>length I6 = MLKEM_N\<close> \<open>length I5 = MLKEM_N\<close>
    \<open>length I4 = MLKEM_N\<close> \<open>length I3 = MLKEM_N\<close> \<open>length I2 = MLKEM_N\<close> \<open>length I1 = MLKEM_N\<close>
    unfolding I1_def I2_def I3_def I4_def I5_def I6_def I7_def
    using len by (simp_all add: invntt_layer_int_length)
  \<comment> \<open>Build accumulated result from innermost to outermost layer\<close>
  \<comment> \<open>Step 7 (base): NTT layer 7 cancels directly\<close>
  have h7: \<open>ntt_outer_loop_int 64 1 I7 ! i mod MLKEM_Q = 2 * cs ! i mod MLKEM_Q\<close>
  proof -
    have \<open>ntt_outer_loop_int 64 1 I7 = ntt_outer_loop_int 128 0 (ntt_layer_int 7 I7)\<close>
      using ntt_outer_loop_step_layer[where l=7] by simp
    moreover have \<open>ntt_outer_loop_int 128 0 (ntt_layer_int 7 I7) = ntt_layer_int 7 I7\<close> by simp
    moreover have \<open>\<forall>j<MLKEM_N. ntt_layer_int 7 I7 ! j mod MLKEM_Q = 2 * cs ! j mod MLKEM_Q\<close>
      unfolding I7_def using ntt_invntt_layer_inverse[of cs 7] len by auto
    ultimately show ?thesis using i_lt by auto
  qed
  \<comment> \<open>Step 6: accumulate 2^2\<close>
  have h6: \<open>ntt_outer_loop_int 32 2 I6 ! i mod MLKEM_Q = 2^2 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. ntt_layer_int 6 I6 ! j mod MLKEM_Q = I7 ! j * 2 mod MLKEM_Q\<close>
      unfolding I6_def using ntt_invntt_layer_inverse[of I7 6] by (auto simp: mult.commute[of 2])
    have \<open>ntt_outer_loop_int 32 2 I6 ! i mod MLKEM_Q =
      ntt_outer_loop_int 64 1 (ntt_layer_int 6 I6) ! i mod MLKEM_Q\<close>
      using ntt_outer_loop_step_layer[where l=6] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 64 1 I7 ! i * 2 mod MLKEM_Q\<close>
      using ntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=1]
      by (simp add: ntt_layer_int_length)
    also have \<open>\<dots> = 2 * cs ! i * 2 mod MLKEM_Q\<close> by (rule mod_mult_cong[OF h7 refl])
    also have \<open>\<dots> = 2^2 * cs ! i mod MLKEM_Q\<close> by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 5: accumulate 2^3\<close>
  have h5: \<open>ntt_outer_loop_int 16 3 I5 ! i mod MLKEM_Q = 2^3 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. ntt_layer_int 5 I5 ! j mod MLKEM_Q = I6 ! j * 2 mod MLKEM_Q\<close>
      unfolding I5_def using ntt_invntt_layer_inverse[of I6 5] by (auto simp: mult.commute[of 2])
    have \<open>ntt_outer_loop_int 16 3 I5 ! i mod MLKEM_Q =
      ntt_outer_loop_int 32 2 (ntt_layer_int 5 I5) ! i mod MLKEM_Q\<close>
      using ntt_outer_loop_step_layer[where l=5] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 32 2 I6 ! i * 2 mod MLKEM_Q\<close>
      using ntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=2]
      by (simp add: ntt_layer_int_length)
    also have \<open>\<dots> = 2^2 * cs ! i * 2 mod MLKEM_Q\<close> by (rule mod_mult_cong[OF h6 refl])
    also have \<open>\<dots> = 2^3 * cs ! i mod MLKEM_Q\<close> by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 4: accumulate 2^4\<close>
  have h4: \<open>ntt_outer_loop_int 8 4 I4 ! i mod MLKEM_Q = 2^4 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. ntt_layer_int 4 I4 ! j mod MLKEM_Q = I5 ! j * 2 mod MLKEM_Q\<close>
      unfolding I4_def using ntt_invntt_layer_inverse[of I5 4] by (auto simp: mult.commute[of 2])
    have \<open>ntt_outer_loop_int 8 4 I4 ! i mod MLKEM_Q =
      ntt_outer_loop_int 16 3 (ntt_layer_int 4 I4) ! i mod MLKEM_Q\<close>
      using ntt_outer_loop_step_layer[where l=4] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 16 3 I5 ! i * 2 mod MLKEM_Q\<close>
      using ntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=3]
      by (simp add: ntt_layer_int_length)
    also have \<open>\<dots> = 2^3 * cs ! i * 2 mod MLKEM_Q\<close> by (rule mod_mult_cong[OF h5 refl])
    also have \<open>\<dots> = 2^4 * cs ! i mod MLKEM_Q\<close> by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 3: accumulate 2^5\<close>
  have h3: \<open>ntt_outer_loop_int 4 5 I3 ! i mod MLKEM_Q = 2^5 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. ntt_layer_int 3 I3 ! j mod MLKEM_Q = I4 ! j * 2 mod MLKEM_Q\<close>
      unfolding I3_def using ntt_invntt_layer_inverse[of I4 3] by (auto simp: mult.commute[of 2])
    have \<open>ntt_outer_loop_int 4 5 I3 ! i mod MLKEM_Q =
      ntt_outer_loop_int 8 4 (ntt_layer_int 3 I3) ! i mod MLKEM_Q\<close>
      using ntt_outer_loop_step_layer[where l=3] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 8 4 I4 ! i * 2 mod MLKEM_Q\<close>
      using ntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=4]
      by (simp add: ntt_layer_int_length)
    also have \<open>\<dots> = 2^4 * cs ! i * 2 mod MLKEM_Q\<close> by (rule mod_mult_cong[OF h4 refl])
    also have \<open>\<dots> = 2^5 * cs ! i mod MLKEM_Q\<close> by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 2: accumulate 2^6\<close>
  have h2: \<open>ntt_outer_loop_int 2 6 I2 ! i mod MLKEM_Q = 2^6 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. ntt_layer_int 2 I2 ! j mod MLKEM_Q = I3 ! j * 2 mod MLKEM_Q\<close>
      unfolding I2_def using ntt_invntt_layer_inverse[of I3 2] by (auto simp: mult.commute[of 2])
    have \<open>ntt_outer_loop_int 2 6 I2 ! i mod MLKEM_Q =
      ntt_outer_loop_int 4 5 (ntt_layer_int 2 I2) ! i mod MLKEM_Q\<close>
      using ntt_outer_loop_step_layer[where l=2] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 4 5 I3 ! i * 2 mod MLKEM_Q\<close>
      using ntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=5]
      by (simp add: ntt_layer_int_length)
    also have \<open>\<dots> = 2^5 * cs ! i * 2 mod MLKEM_Q\<close> by (rule mod_mult_cong[OF h3 refl])
    also have \<open>\<dots> = 2^6 * cs ! i mod MLKEM_Q\<close> by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 1: accumulate 2^7\<close>
  have h1: \<open>ntt_outer_loop_int 1 7 I1 ! i mod MLKEM_Q = 2^7 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. ntt_layer_int 1 I1 ! j mod MLKEM_Q = I2 ! j * 2 mod MLKEM_Q\<close>
      unfolding I1_def using ntt_invntt_layer_inverse[of I2 1] by (auto simp: mult.commute[of 2])
    have \<open>ntt_outer_loop_int 1 7 I1 ! i mod MLKEM_Q =
      ntt_outer_loop_int 2 6 (ntt_layer_int 1 I1) ! i mod MLKEM_Q\<close>
      using ntt_outer_loop_step_layer[where l=1] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 2 6 I2 ! i * 2 mod MLKEM_Q\<close>
      using ntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=6]
      by (simp add: ntt_layer_int_length)
    also have \<open>\<dots> = 2^6 * cs ! i * 2 mod MLKEM_Q\<close> by (rule mod_mult_cong[OF h2 refl])
    also have \<open>\<dots> = 2^7 * cs ! i mod MLKEM_Q\<close> by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis using h1 invntt_eq by simp
qed

text \<open>Reverse composition: invNTT(NTT(cs)) gives the same @{text "2^7"} factor.\<close>

lemma invntt_ntt_outer_compose:
  assumes len: \<open>length cs = MLKEM_N\<close>
      and i_lt: \<open>i < MLKEM_N\<close>
    shows \<open>invntt_outer_loop_int 7 (ntt_outer_loop_int 1 7 cs) ! i mod MLKEM_Q =
           (2::int)^7 * cs ! i mod MLKEM_Q\<close>
proof -
  \<comment> \<open>Unfold NTT layers 1 through 7\<close>
  define N1 where \<open>N1 = ntt_layer_int 1 cs\<close>
  define N2 where \<open>N2 = ntt_layer_int 2 N1\<close>
  define N3 where \<open>N3 = ntt_layer_int 3 N2\<close>
  define N4 where \<open>N4 = ntt_layer_int 4 N3\<close>
  define N5 where \<open>N5 = ntt_layer_int 5 N4\<close>
  define N6 where \<open>N6 = ntt_layer_int 6 N5\<close>
  define N7 where \<open>N7 = ntt_layer_int 7 N6\<close>
  have ntt_eq: \<open>ntt_outer_loop_int 1 7 cs = N7\<close>
  proof -
    have \<open>ntt_outer_loop_int 1 7 cs = ntt_outer_loop_int 2 6 N1\<close>
      unfolding N1_def using ntt_outer_loop_step_layer[where l=1] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 4 5 N2\<close>
      unfolding N2_def using ntt_outer_loop_step_layer[where l=2] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 8 4 N3\<close>
      unfolding N3_def using ntt_outer_loop_step_layer[where l=3] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 16 3 N4\<close>
      unfolding N4_def using ntt_outer_loop_step_layer[where l=4] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 32 2 N5\<close>
      unfolding N5_def using ntt_outer_loop_step_layer[where l=5] by simp
    also have \<open>\<dots> = ntt_outer_loop_int 64 1 N6\<close>
      unfolding N6_def using ntt_outer_loop_step_layer[where l=6] by simp
    also have \<open>\<dots> = N7\<close>
      unfolding N7_def using ntt_outer_loop_step_layer[where l=7] by simp
    finally show ?thesis .
  qed
  \<comment> \<open>Length lemmas\<close>
  have [simp]: \<open>length N1 = MLKEM_N\<close> \<open>length N2 = MLKEM_N\<close> \<open>length N3 = MLKEM_N\<close>
      \<open>length N4 = MLKEM_N\<close> \<open>length N5 = MLKEM_N\<close> \<open>length N6 = MLKEM_N\<close> \<open>length N7 = MLKEM_N\<close>
    unfolding N1_def N2_def N3_def N4_def N5_def N6_def N7_def using len
      by (simp_all add: ntt_layer_int_length)
  \<comment> \<open>Base case: invNTT layer 1 cancels NTT layer 1\<close>
  have h1: \<open>invntt_outer_loop_int 1 N1 ! i mod MLKEM_Q = 2 * cs ! i mod MLKEM_Q\<close>
  proof -
    have \<open>invntt_outer_loop_int 1 N1 = invntt_layer_int 1 N1\<close>
      by (simp only: One_nat_def invntt_outer_loop_step invntt_outer_loop_int.simps(1))
    moreover have \<open>\<forall>j<MLKEM_N. invntt_layer_int 1 N1 ! j mod MLKEM_Q = 2 * cs ! j mod MLKEM_Q\<close>
      unfolding N1_def using invntt_ntt_layer_inverse[of cs 1] len by auto
    ultimately show ?thesis
      using i_lt by auto
  qed
  \<comment> \<open>Step 2: accumulate 2^2\<close>
  have h2: \<open>invntt_outer_loop_int 2 N2 ! i mod MLKEM_Q = 2^2 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. invntt_layer_int 2 N2 ! j mod MLKEM_Q = N1 ! j * 2 mod MLKEM_Q\<close>
      unfolding N2_def using invntt_ntt_layer_inverse[of N1 2] by (auto simp: mult.commute[of 2])
    have \<open>invntt_outer_loop_int 2 N2 ! i mod MLKEM_Q =
            invntt_outer_loop_int 1 (invntt_layer_int 2 N2) ! i mod MLKEM_Q\<close>
      using invntt_outer_loop_step[where n=1] by (simp add: eval_nat_numeral del: invntt_outer_loop_int.simps(2))
    also have \<open>\<dots> = invntt_outer_loop_int 1 N1 ! i * 2 mod MLKEM_Q\<close>
      using invntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=1] by (simp add: invntt_layer_int_length)
    also have \<open>\<dots> = 2 * cs ! i * 2 mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF h1 refl])
    also have \<open>\<dots> = 2^2 * cs ! i mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 3: accumulate 2^3\<close>
  have h3: \<open>invntt_outer_loop_int 3 N3 ! i mod MLKEM_Q = 2^3 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. invntt_layer_int 3 N3 ! j mod MLKEM_Q = N2 ! j * 2 mod MLKEM_Q\<close>
      unfolding N3_def using invntt_ntt_layer_inverse[of N2 3] by (auto simp: mult.commute[of 2])
    have \<open>invntt_outer_loop_int 3 N3 ! i mod MLKEM_Q =
              invntt_outer_loop_int 2 (invntt_layer_int 3 N3) ! i mod MLKEM_Q\<close>
      using invntt_outer_loop_step[where n=2] by (simp add: eval_nat_numeral del: invntt_outer_loop_int.simps(2))
    also have \<open>\<dots> = invntt_outer_loop_int 2 N2 ! i * 2 mod MLKEM_Q\<close>
      using invntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=2] by (simp add: invntt_layer_int_length)
    also have \<open>\<dots> = 2^2 * cs ! i * 2 mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF h2 refl])
    also have \<open>\<dots> = 2^3 * cs ! i mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 4: accumulate 2^4\<close>
  have h4: \<open>invntt_outer_loop_int 4 N4 ! i mod MLKEM_Q = 2^4 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. invntt_layer_int 4 N4 ! j mod MLKEM_Q = N3 ! j * 2 mod MLKEM_Q\<close>
      unfolding N4_def using invntt_ntt_layer_inverse[of N3 4] by (auto simp: mult.commute[of 2])
    have \<open>invntt_outer_loop_int 4 N4 ! i mod MLKEM_Q =
            invntt_outer_loop_int 3 (invntt_layer_int 4 N4) ! i mod MLKEM_Q\<close>
      using invntt_outer_loop_step[where n=3] by (simp add: eval_nat_numeral del: invntt_outer_loop_int.simps(2))
    also have \<open>\<dots> = invntt_outer_loop_int 3 N3 ! i * 2 mod MLKEM_Q\<close>
      using invntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=3] by (simp add: invntt_layer_int_length)
    also have \<open>\<dots> = 2^3 * cs ! i * 2 mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF h3 refl])
    also have \<open>\<dots> = 2^4 * cs ! i mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 5: accumulate 2^5\<close>
  have h5: \<open>invntt_outer_loop_int 5 N5 ! i mod MLKEM_Q = 2^5 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. invntt_layer_int 5 N5 ! j mod MLKEM_Q = N4 ! j * 2 mod MLKEM_Q\<close>
      unfolding N5_def using invntt_ntt_layer_inverse[of N4 5] by (auto simp: mult.commute[of 2])
    have \<open>invntt_outer_loop_int 5 N5 ! i mod MLKEM_Q =
            invntt_outer_loop_int 4 (invntt_layer_int 5 N5) ! i mod MLKEM_Q\<close>
      using invntt_outer_loop_step[where n=4] by (simp add: eval_nat_numeral del: invntt_outer_loop_int.simps(2))
    also have \<open>\<dots> = invntt_outer_loop_int 4 N4 ! i * 2 mod MLKEM_Q\<close>
      using invntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=4] by (simp add: invntt_layer_int_length)
    also have \<open>\<dots> = 2^4 * cs ! i * 2 mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF h4 refl])
    also have \<open>\<dots> = 2^5 * cs ! i mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 6: accumulate 2^6\<close>
  have h6: \<open>invntt_outer_loop_int 6 N6 ! i mod MLKEM_Q = 2^6 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. invntt_layer_int 6 N6 ! j mod MLKEM_Q = N5 ! j * 2 mod MLKEM_Q\<close>
      unfolding N6_def using invntt_ntt_layer_inverse[of N5 6] by (auto simp: mult.commute[of 2])
    have \<open>invntt_outer_loop_int 6 N6 ! i mod MLKEM_Q =
            invntt_outer_loop_int 5 (invntt_layer_int 6 N6) ! i mod MLKEM_Q\<close>
      using invntt_outer_loop_step[where n=5] by (simp add: eval_nat_numeral del: invntt_outer_loop_int.simps(2))
    also have \<open>\<dots> = invntt_outer_loop_int 5 N5 ! i * 2 mod MLKEM_Q\<close>
      using invntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=5] by (simp add: invntt_layer_int_length)
    also have \<open>\<dots> = 2^5 * cs ! i * 2 mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF h5 refl])
    also have \<open>\<dots> = 2^6 * cs ! i mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 7: accumulate 2^7\<close>
  have h7: \<open>invntt_outer_loop_int 7 N7 ! i mod MLKEM_Q = 2^7 * cs ! i mod MLKEM_Q\<close>
  proof -
    have cancel: \<open>\<forall>j<MLKEM_N. invntt_layer_int 7 N7 ! j mod MLKEM_Q = N6 ! j * 2 mod MLKEM_Q\<close>
      unfolding N7_def using invntt_ntt_layer_inverse[of N6 7] by (auto simp: mult.commute[of 2])
    have \<open>invntt_outer_loop_int 7 N7 ! i mod MLKEM_Q =
            invntt_outer_loop_int 6 (invntt_layer_int 7 N7) ! i mod MLKEM_Q\<close>
      using invntt_outer_loop_step[where n=6] by (simp add: eval_nat_numeral del: invntt_outer_loop_int.simps(2))
    also have \<open>\<dots> = invntt_outer_loop_int 6 N6 ! i * 2 mod MLKEM_Q\<close>
      using invntt_outer_loop_linear_cong[OF cancel _ _ i_lt, where n=6] by (simp add: invntt_layer_int_length)
    also have \<open>\<dots> = 2^6 * cs ! i * 2 mod MLKEM_Q\<close>
      by (rule mod_mult_cong[OF h6 refl])
    also have \<open>\<dots> = 2^7 * cs ! i mod MLKEM_Q\<close>
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using h7 ntt_eq by simp
qed

text \<open>Direction 2 (easier): @{text "NTT(invNTT(cs)) \<equiv> cs \<sqdot> R (mod Q)"}.
  The 7 layer pairs each contribute a factor of 2, giving @{text "2^7 = 128"}.
  The prescaling by 1441 contributes @{text "1441 \<sqdot> R^{-1} \<equiv> 2^9 (mod Q)"}.
  Together: @{text "128 \<sqdot> 2^9 = 2^16 = R"}.\<close>

theorem poly_ntt_invntt_tomont:
  assumes \<open>length cs = 256\<close>
      and \<open>i < 256\<close>
    shows \<open>poly_ntt_int (poly_invntt_tomont_int cs) ! i mod MLKEM_Q =
             cs ! i * 2^16 mod MLKEM_Q\<close>
unfolding poly_ntt_int_def poly_invntt_tomont_int_def
  using ntt_invntt_outer_compose[of \<open>List.map (\<lambda>c. fqmul_int c 1441) cs\<close> i]
    assms prescale_factor[of \<open>cs ! i\<close>] by simp

text \<open>Direction 1: @{text "invNTT(NTT(cs)) \<equiv> cs \<sqdot> R (mod Q)"}.
  Uses linearity to move the prescaling past the NTT layers.\<close>

theorem poly_invntt_tomont_ntt:
  assumes \<open>length cs = 256\<close>
      and \<open>i < 256\<close>
    shows \<open>poly_invntt_tomont_int (poly_ntt_int cs) ! i mod MLKEM_Q =
             cs ! i * 2^16 mod MLKEM_Q\<close>
proof -
  define ntt_cs where
    \<open>ntt_cs = ntt_outer_loop_int 1 7 cs\<close>
  have len_ntt: \<open>length ntt_cs = MLKEM_N\<close>
    unfolding ntt_cs_def using assms by (simp add: ntt_outer_loop_int_length)
  have cong: \<open>\<forall>j < MLKEM_N. (List.map (\<lambda>c. fqmul_int c 1441) ntt_cs) ! j mod MLKEM_Q =
                ntt_cs ! j * fqmul_int 1 1441 mod MLKEM_Q\<close>
  proof (intro allI impI)
       fix j
    assume \<open>j < MLKEM_N\<close>
    then show \<open>(List.map (\<lambda>c. fqmul_int c 1441) ntt_cs) ! j mod MLKEM_Q =
              ntt_cs ! j * fqmul_int 1 1441 mod MLKEM_Q\<close>
      using len_ntt fqmul_int_linear_mod[of 1 \<open>ntt_cs ! j\<close> 1441] by (simp add: mult.commute)
  qed
  have step1: \<open>invntt_outer_loop_int 7 (List.map (\<lambda>c. fqmul_int c 1441) ntt_cs) ! i mod MLKEM_Q =
                  invntt_outer_loop_int 7 ntt_cs ! i * fqmul_int 1 1441 mod MLKEM_Q\<close>
    using invntt_outer_loop_linear_cong[OF cong _ len_ntt assms(2), where n=7] by (simp add: len_ntt)
  also have \<open>\<dots> = 2^7 * cs ! i * fqmul_int 1 1441 mod MLKEM_Q\<close>
    by (rule mod_mult_cong[OF invntt_ntt_outer_compose[OF assms, folded ntt_cs_def] refl])
  also have \<open>\<dots> = cs ! i * (128 * fqmul_int 1 1441) mod MLKEM_Q\<close>
    by (simp add: algebra_simps)
  also have \<open>\<dots> = cs ! i * 2^16 mod MLKEM_Q\<close>
  proof -
    have eq: \<open>128 * fqmul_int 1 1441 mod MLKEM_Q = 2^16 mod MLKEM_Q\<close>
      using prescale_factor[of 1] by simp
    show ?thesis
      using mod_mult_right_eq[of \<open>cs ! i\<close> \<open>128 * fqmul_int 1 1441\<close> MLKEM_Q]
        mod_mult_right_eq[of \<open>cs ! i\<close> \<open>2^16\<close> MLKEM_Q] eq by simp
  qed
  finally show ?thesis
    unfolding poly_invntt_tomont_int_def poly_ntt_int_def ntt_cs_def .
qed

(*<*)
end
(*>*)

