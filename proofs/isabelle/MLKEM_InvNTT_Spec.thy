(*<*)
theory MLKEM_InvNTT_Spec
  imports MLKEM_NTT_Spec
begin
(*>*)

text \<open>
  Abstract specification of the inverse NTT (Number Theoretic Transform)
  for ML-KEM polynomials.  Mirrors the structure of @{text MLKEM_NTT_Spec}
  with reversed butterfly direction: the sum is Barrett-reduced while
  the difference is Montgomery-multiplied by the twiddle factor.
  Coefficient-bound propagation and overflow safety are established
  for all loop levels.
\<close>

section \<open>Inverse NTT Specification\<close>

text_raw \<open>
\begin{figure}[ht]
\centering
\begin{tikzpicture}[>=Stealth, node distance=2.8cm and 3.5cm,
    every node/.style={font=\small},
    io/.style={fill=mlklightblue, draw=mlkblue, rounded corners=3pt,
               inner sep=4pt}]
  % Input nodes
  \node[io] (a) {$a$};
  \node[io, below=1.6cm of a] (b) {$b$};
  % Output nodes
  \node[io, right=5cm of a] (out1) {$\mathrm{barrett}(a + b)$};
  \node[io, right=5cm of b] (out2) {$\mathit{fqmul}(b - a,\;\zeta)$};
  % Arrows
  \draw[->,thick,mlkblue] (a) -- (out1);
  \draw[->,thick,mlkblue] (a) -- (out2);
  \draw[->,thick,mlkblue] (b) -- (out1);
  \draw[->,thick,mlkblue] (b) -- node[below,pos=0.4] {$\times\,\zeta$} (out2);
\end{tikzpicture}
\caption{Inverse NTT butterfly: the sum is Barrett-reduced to keep
  coefficients bounded by~$q$, while the difference is
  Montgomery-multiplied by the twiddle factor~$\zeta$.}
\label{fig:invntt-butterfly}
\end{figure}
\<close>

subsection \<open>Definitions\<close>

text \<open>The inverse NTT butterfly applies Barrett reduction to the sum
  and Montgomery multiplication to the difference.\<close>

definition invntt_butterfly_int :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>invntt_butterfly_int zeta j blen cs \<equiv>
     let t   = cs ! j;
         cs' = cs[j := barrett_reduce_int (t + cs ! (j + blen))]
      in cs'[j + blen := fqmul_int (cs ! (j + blen) - t) zeta]\<close>

fun invntt_inner_loop_int :: \<open>int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>invntt_inner_loop_int zeta off blen 0         cs = cs\<close>
| \<open>invntt_inner_loop_int zeta off blen (Suc cnt) cs =
     invntt_inner_loop_int zeta (Suc off) blen cnt
       (invntt_butterfly_int zeta off blen cs)\<close>

fun invntt_middle_loop_int :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat \<times> int list\<close> where
  \<open>invntt_middle_loop_int k blen 0               num_blocks cs = (k, cs)\<close>
| \<open>invntt_middle_loop_int k blen (Suc remaining) num_blocks cs =
     (let block = num_blocks - Suc remaining;
          off   = block * (2 * blen);
          zeta  = zetas_int ! k;
          cs'   = invntt_inner_loop_int zeta off blen blen cs
       in invntt_middle_loop_int (k - 1) blen remaining num_blocks cs')\<close>

fun invntt_outer_loop_int :: \<open>nat \<Rightarrow> int list \<Rightarrow> int list\<close> where
  \<open>invntt_outer_loop_int 0       cs = cs\<close>
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

subsection \<open>Inner Loop Properties\<close>

text \<open>Structural lemmas for the inverse NTT inner loop: length preservation,
  snoc decomposition, and per-position value characterisation.\<close>

(*<*)
lemma invntt_butterfly_int_length:
  shows \<open>length (invntt_butterfly_int z j blen cs) = length cs\<close>
unfolding invntt_butterfly_int_def Let_def by simp

lemma invntt_inner_loop_int_snoc:
  shows \<open>invntt_inner_loop_int z off blen (Suc m) cs =
         invntt_butterfly_int z (off + m) blen (invntt_inner_loop_int z off blen m cs)\<close>
proof (induct m arbitrary: off cs)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have \<open>invntt_inner_loop_int z off blen (Suc (Suc m)) cs =
        invntt_inner_loop_int z (Suc off) blen (Suc m) (invntt_butterfly_int z off blen cs)\<close>
    by simp
  also have \<open>\<dots> = invntt_butterfly_int z (Suc off + m) blen
        (invntt_inner_loop_int z (Suc off) blen m (invntt_butterfly_int z off blen cs))\<close>
    by (rule Suc)
  also have \<open>Suc off + m = off + Suc m\<close>
    by simp
  also have \<open>invntt_inner_loop_int z (Suc off) blen m (invntt_butterfly_int z off blen cs)
           = invntt_inner_loop_int z off blen (Suc m) cs\<close>
    by simp
  finally show ?case
    .
qed

lemma invntt_inner_loop_int_length:
  shows \<open>length (invntt_inner_loop_int z off blen cnt cs) = length cs\<close>
by (induction cnt arbitrary: off cs) (simp_all add: invntt_butterfly_int_length)

lemma invntt_butterfly_int_nth_other:
  assumes \<open>i \<noteq> j\<close>
      and \<open>i \<noteq> j + blen\<close>
    shows \<open>invntt_butterfly_int zeta j blen cs ! i = cs ! i\<close>
unfolding invntt_butterfly_int_def Let_def using assms by simp

lemma invntt_inner_loop_int_nth_unchanged:
  assumes \<open>i \<notin> {off..<off+cnt}\<close>
      and \<open>i \<notin> {off+blen..<off+cnt+blen}\<close>
    shows \<open>invntt_inner_loop_int z off blen cnt cs ! i = cs ! i\<close>
using assms proof (induct cnt arbitrary: off cs)
  case 0 then show ?case by simp
next
  case (Suc cnt)
  from Suc.prems have \<open>i \<noteq> off\<close> \<open>i \<noteq> off + blen\<close>
    by auto
  from Suc.prems have ih1: \<open>i \<notin> {Suc off..<Suc off+cnt}\<close>
    by auto
  from Suc.prems have ih2: \<open>i \<notin> {Suc off+blen..<Suc off+cnt+blen}\<close>
    by auto
  have \<open>invntt_inner_loop_int z off blen (Suc cnt) cs ! i =
        invntt_inner_loop_int z (Suc off) blen cnt (invntt_butterfly_int z off blen cs) ! i\<close>
    by simp
  also have \<open>\<dots> = (invntt_butterfly_int z off blen cs) ! i\<close>
    by (rule Suc.hyps[OF ih1 ih2])
  also have \<open>\<dots> = cs ! i\<close>
    by (rule invntt_butterfly_int_nth_other[OF \<open>i \<noteq> off\<close> \<open>i \<noteq> off + blen\<close>])
  finally show ?case .
qed

lemma invntt_inner_loop_int_low_val:
  assumes \<open>m < cnt\<close>
      and \<open>cnt \<le> blen\<close>
      and \<open>off + 2 * blen \<le> length cs\<close>
    shows \<open>invntt_inner_loop_int z off blen cnt cs ! (off + m) =
              barrett_reduce_int (cs ! (off + m) + cs ! (off + m + blen))\<close>
using assms proof (induct cnt arbitrary: m)
  case 0 then show ?case by simp
next
  case (Suc cnt)
  have snoc: \<open>invntt_inner_loop_int z off blen (Suc cnt) cs =
                invntt_butterfly_int z (off + cnt) blen (invntt_inner_loop_int z off blen cnt cs)\<close>
    by (rule invntt_inner_loop_int_snoc)
  define prev where \<open>prev = invntt_inner_loop_int z off blen cnt cs\<close>
  have len_prev: \<open>length prev = length cs\<close> unfolding prev_def
    by (rule invntt_inner_loop_int_length)
  have p1: \<open>prev ! (off + cnt) = cs ! (off + cnt)\<close>
    unfolding prev_def by (rule invntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  have p2: \<open>prev ! (off + cnt + blen) = cs ! (off + cnt + blen)\<close>
    unfolding prev_def by (rule invntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  show ?case
  proof (cases \<open>m = cnt\<close>)
    case True
    have \<open>off + cnt + blen < length prev\<close>
      using Suc.prems len_prev by simp
    have ne: \<open>off + cnt + blen \<noteq> off + cnt\<close>
      using Suc.prems by simp
    show ?thesis using True snoc p1 p2 ne \<open>off + cnt + blen < length prev\<close>
      by (simp add: invntt_butterfly_int_def Let_def prev_def[symmetric])
  next
    case False
    with Suc.prems have \<open>m < cnt\<close> by simp
    have \<open>off + m \<noteq> off + cnt\<close> using \<open>m < cnt\<close> by simp
    have \<open>off + m \<noteq> off + cnt + blen\<close> using \<open>m < cnt\<close> Suc.prems by simp
    have \<open>invntt_inner_loop_int z off blen (Suc cnt) cs ! (off + m) = prev ! (off + m)\<close>
      using snoc invntt_butterfly_int_nth_other[OF \<open>off + m \<noteq> off + cnt\<close> \<open>off + m \<noteq> off + cnt + blen\<close>]
        by (simp add: prev_def)
    also have \<open>\<dots> = barrett_reduce_int (cs ! (off + m) + cs ! (off + m + blen))\<close>
      unfolding prev_def by (rule Suc.hyps[OF \<open>m < cnt\<close>]) (use Suc.prems in auto)
    finally show ?thesis .
  qed
qed

lemma invntt_inner_loop_int_high_val:
  assumes \<open>m < cnt\<close> \<open>cnt \<le> blen\<close> \<open>off + 2 * blen \<le> length cs\<close>
    shows \<open>invntt_inner_loop_int z off blen cnt cs ! (off + m + blen) =
              fqmul_int (cs ! (off + m + blen) - cs ! (off + m)) z\<close>
using assms proof (induct cnt arbitrary: m)
  case 0 then show ?case by simp
next
  case (Suc cnt)
  have snoc: \<open>invntt_inner_loop_int z off blen (Suc cnt) cs =
                invntt_butterfly_int z (off + cnt) blen (invntt_inner_loop_int z off blen cnt cs)\<close>
    by (rule invntt_inner_loop_int_snoc)
  define prev where \<open>prev = invntt_inner_loop_int z off blen cnt cs\<close>
  have len_prev: \<open>length prev = length cs\<close> unfolding prev_def
    by (rule invntt_inner_loop_int_length)
  have p1: \<open>prev ! (off + cnt) = cs ! (off + cnt)\<close>
    unfolding prev_def by (rule invntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  have p2: \<open>prev ! (off + cnt + blen) = cs ! (off + cnt + blen)\<close>
    unfolding prev_def by (rule invntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  show ?case
  proof (cases \<open>m = cnt\<close>)
    case True
    have len1: \<open>off + cnt < length prev\<close> using Suc.prems len_prev by simp
    have len2: \<open>off + cnt + blen < length prev\<close> using Suc.prems len_prev by simp
    have ne: \<open>off + cnt + blen \<noteq> off + cnt\<close> using Suc.prems by simp
    show ?thesis using True snoc p1 p2 ne len1 len2
      by (simp add: invntt_butterfly_int_def Let_def prev_def[symmetric])
  next
    case False
    with Suc.prems have mc: \<open>m < cnt\<close> by simp
    have ne1: \<open>off + m + blen \<noteq> off + cnt\<close> using Suc.prems by simp
    have ne2: \<open>off + m + blen \<noteq> off + cnt + blen\<close> using mc by simp
    have \<open>invntt_inner_loop_int z off blen (Suc cnt) cs ! (off + m + blen) = prev ! (off + m + blen)\<close>
      using snoc invntt_butterfly_int_nth_other[OF ne1 ne2] by (simp add: prev_def)
    also have \<open>\<dots> = fqmul_int (cs ! (off + m + blen) - cs ! (off + m)) z\<close>
      unfolding prev_def by (rule Suc.hyps[OF mc]) (use Suc.prems in auto)
    finally show ?thesis .
  qed
qed
(*>*)

subsection \<open>Middle Loop Properties\<close>

text \<open>Structural lemmas for the middle and outer loops: length preservation,
  k-index tracking, snoc decomposition, and position-unchanged results.\<close>

(*<*)
lemma invntt_middle_loop_int_length:
  shows \<open>length (snd (invntt_middle_loop_int k blen rem nb cs)) = length cs\<close>
by (induction rem arbitrary: k cs) (auto simp: case_prod_beta Let_def invntt_inner_loop_int_length)

lemma invntt_layer_int_length:
  shows \<open>length (invntt_layer_int l cs) = length cs\<close>
unfolding invntt_layer_int_def by (rule invntt_middle_loop_int_length)

lemma invntt_outer_loop_int_length:
  shows \<open>length (invntt_outer_loop_int n cs) = length cs\<close>
by (induction n arbitrary: cs) (auto simp: case_prod_beta Let_def invntt_middle_loop_int_length)

text \<open>Inverse NTT middle loop: k-index tracking (k decrements).\<close>

lemma invntt_middle_loop_int_fst:
  shows \<open>fst (invntt_middle_loop_int k blen rem nb cs) = k - rem\<close>
by (induction rem arbitrary: k cs) (auto simp: case_prod_beta Let_def)

text \<open>Snoc decomposition for the inverse NTT middle loop: processing @{term \<open>Suc j\<close>} blocks
  equals processing @{term j} blocks then applying one more inner loop
  at the next block offset. Analogous to @{thm ntt_middle_loop_int_snoc_gen}
  but with k decrementing instead of incrementing.\<close>

lemma invntt_middle_loop_int_snoc_gen:
  shows \<open>snd (invntt_middle_loop_int k blen (Suc j) (s + Suc j) cs) =
         invntt_inner_loop_int (zetas_int ! (k - j)) ((s + j) * (2 * blen)) blen blen
           (snd (invntt_middle_loop_int k blen j (s + j) cs))\<close>
proof (induct j arbitrary: k s cs)
  case 0
  then show ?case
    by (simp add: case_prod_beta Let_def)
next
  case (Suc j)
  \<comment> \<open>Unfold one step: processes block at offset s\<close>
  have lhs: \<open>invntt_middle_loop_int k blen (Suc (Suc j)) (s + Suc (Suc j)) cs =
        invntt_middle_loop_int (k - 1) blen (Suc j) (s + Suc (Suc j))
          (invntt_inner_loop_int (zetas_int ! k) (s * (2 * blen)) blen blen cs)\<close>
    by (simp add: case_prod_beta Let_def)
  define cs' where
    \<open>cs' = invntt_inner_loop_int (zetas_int ! k) (s * (2 * blen)) blen blen cs\<close>
  \<comment> \<open>Rewrite @{term \<open>s + Suc (Suc j)\<close>} = @{term \<open>Suc s + Suc j\<close>}\<close>
  have \<open>snd (invntt_middle_loop_int (k - 1) blen (Suc j) (Suc s + Suc j) cs') =
        invntt_inner_loop_int (zetas_int ! ((k - 1) - j)) ((Suc s + j) * (2 * blen)) blen blen
          (snd (invntt_middle_loop_int (k - 1) blen j (Suc s + j) cs'))\<close>
    by (rule Suc)
  \<comment> \<open>RHS unfolds the same way\<close>
  moreover have \<open>invntt_middle_loop_int k blen (Suc j) (s + Suc j) cs =
        invntt_middle_loop_int (k - 1) blen j (s + Suc j)
          (invntt_inner_loop_int (zetas_int ! k) (s * (2 * blen)) blen blen cs)\<close>
    by (simp add: case_prod_beta Let_def)
  ultimately show ?case
    using lhs by (simp add: cs'_def)
qed

corollary invntt_middle_loop_int_snoc:
  shows \<open>snd (invntt_middle_loop_int k blen (Suc j) (Suc j) cs) =
         invntt_inner_loop_int (zetas_int ! (k - j)) (j * (2 * blen)) blen blen
           (snd (invntt_middle_loop_int k blen j j cs))\<close>
using invntt_middle_loop_int_snoc_gen[where s=0] by simp

lemma invntt_middle_loop_int_nth_unchanged:
  assumes \<open>j * (2 * blen) \<le> i\<close>
  shows \<open>snd (invntt_middle_loop_int k blen j j cs) ! i = cs ! i\<close>
using assms proof (induct j arbitrary: k cs)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have snoc: \<open>snd (invntt_middle_loop_int k blen (Suc j) (Suc j) cs) =
    invntt_inner_loop_int (zetas_int ! (k - j)) (j * (2 * blen)) blen blen
      (snd (invntt_middle_loop_int k blen j j cs))\<close>
    by (rule invntt_middle_loop_int_snoc)
  define prev where \<open>prev = snd (invntt_middle_loop_int k blen j j cs)\<close>
  from Suc.prems have \<open>j * (2 * blen) \<le> i\<close> by simp
  hence ih: \<open>prev ! i = cs ! i\<close>
    unfolding prev_def by (rule Suc.hyps)
  from Suc.prems have \<open>i \<notin> {j * (2 * blen)..<j * (2 * blen) + blen}\<close> by auto
  moreover from Suc.prems have \<open>i \<notin> {j * (2 * blen) + blen..<j * (2 * blen) + blen + blen}\<close> by auto
  ultimately have \<open>invntt_inner_loop_int (zetas_int ! (k - j)) (j * (2 * blen)) blen blen prev ! i = prev ! i\<close>
    by (rule invntt_inner_loop_int_nth_unchanged)
  with ih snoc show ?case by (simp add: prev_def)
qed
(*>*)

subsection \<open>Bound Propagation\<close>

text \<open>fqmul bound when the second argument is bounded by the max zetas value.
  Since @{term \<open>\<bar>b\<bar> \<le> 1659\<close>} and @{term \<open>\<bar>a\<bar> < 32768\<close>}, the product
  @{term \<open>\<bar>a * b\<bar> < 32768 * MLKEM_Q\<close>} and @{thm fqmul_int_bound_Q} applies.\<close>

lemma fqmul_prescale_bound:
  assumes \<open>\<bar>b\<bar> \<le> 1659\<close> and \<open>\<bar>a\<bar> \<le> 32768\<close>
    shows \<open>\<bar>fqmul_int a b\<bar> < MLKEM_Q\<close>
proof (rule fqmul_int_bound_Q)
  have \<open>\<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>\<close>
    by (rule abs_mult)
  also have \<open>\<dots> \<le> 32768 * 1659\<close>
  proof (rule mult_mono)
    show \<open>\<bar>a\<bar> \<le> 32768\<close>
      by (rule assms(2))
    show \<open>\<bar>b\<bar> \<le> 1659\<close>
      by (rule assms(1))
  qed auto
  also have \<open>\<dots> < 32768 * MLKEM_Q\<close>
    by simp
  finally show \<open>\<bar>a * b\<bar> < 32768 * MLKEM_Q\<close>
    .
qed

lemma fqmul_prescale_bound_sint:
  fixes a :: \<open>16 sword\<close>
  assumes \<open>\<bar>b\<bar> \<le> 1659\<close>
    shows \<open>\<bar>fqmul_int (sint a) b\<bar> < MLKEM_Q\<close>
proof (rule fqmul_prescale_bound[OF assms])
  have \<open>sint a \<ge> -(2^(size a - 1))\<close> and \<open>sint a < 2^(size a - 1)\<close>
    using sint_range_size[of a] by auto
  thus \<open>\<bar>sint a\<bar> \<le> 32768\<close>
    by (auto simp: word_size)
qed

text \<open>Coefficient bound preservation through inverse NTT butterfly and loops.\<close>

lemma invntt_butterfly_int_coeff_bound:
  assumes \<open>coeff_bound MLKEM_Q cs\<close>
      and \<open>j + blen < length cs\<close>
      and \<open>j < length cs\<close>
      and \<open>\<bar>zeta\<bar> \<le> 1659\<close>
    shows \<open>coeff_bound MLKEM_Q (invntt_butterfly_int zeta j blen cs)\<close>
proof -
  from assms(1,2,3) have j_bound: \<open>\<bar>cs ! j\<bar> < MLKEM_Q\<close>
      and jb_bound: \<open>\<bar>cs ! (j + blen)\<bar> < MLKEM_Q\<close>
    unfolding coeff_bound_def by auto
  have sum_range: \<open>-32768 \<le> cs ! j + cs ! (j + blen)\<close>
      \<open>cs ! j + cs ! (j + blen) \<le> 32767\<close>
    using j_bound jb_bound by linarith+
  have barrett_bound: \<open>\<bar>barrett_reduce_int (cs ! j + cs ! (j + blen))\<bar> < MLKEM_Q\<close>
    by (rule barrett_reduce_int_abs_bound_int[OF sum_range])
  have diff_bound: \<open>\<bar>cs ! (j + blen) - cs ! j\<bar> \<le> 32768\<close>
    using j_bound jb_bound by linarith
  have fqmul_bound: \<open>\<bar>fqmul_int (cs ! (j + blen) - cs ! j) zeta\<bar> < MLKEM_Q\<close>
    by (rule fqmul_prescale_bound[OF assms(4) diff_bound])
  show ?thesis
    unfolding invntt_butterfly_int_def Let_def coeff_bound_def
      invntt_butterfly_int_length
    using barrett_bound fqmul_bound assms(1,2,3)
    by (auto simp: nth_list_update coeff_bound_def)
qed

lemma invntt_inner_loop_int_coeff_bound:
  assumes \<open>coeff_bound MLKEM_Q cs\<close>
      and \<open>off + 2 * blen \<le> length cs\<close>
      and \<open>cnt \<le> blen\<close>
      and \<open>\<bar>zeta\<bar> \<le> 1659\<close>
    shows \<open>coeff_bound MLKEM_Q (invntt_inner_loop_int zeta off blen cnt cs)\<close>
proof -
  from assms(2,3) have \<open>off + cnt + blen \<le> length cs\<close>
    by linarith
  thus ?thesis using assms(1)
  proof (induct cnt arbitrary: off cs)
    case 0
    then show ?case by simp
  next
    case (Suc cnt)
    have off_lt: \<open>off < length cs\<close>
      using Suc.prems(1) by linarith
    have off_blen_lt: \<open>off + blen < length cs\<close>
      using Suc.prems(1) by linarith
    have cb': \<open>coeff_bound MLKEM_Q (invntt_butterfly_int zeta off blen cs)\<close>
      by (rule invntt_butterfly_int_coeff_bound[OF Suc.prems(2) off_blen_lt off_lt assms(4)])
    have len': \<open>Suc off + cnt + blen \<le> length (invntt_butterfly_int zeta off blen cs)\<close>
      using Suc.prems(1) by (simp add: invntt_butterfly_int_length)
    show ?case
      by simp (rule Suc.hyps[OF len' cb'])
  qed
qed

lemma invntt_middle_loop_int_coeff_bound:
  assumes \<open>coeff_bound MLKEM_Q cs\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>length cs = MLKEM_N\<close>
      and \<open>j \<le> 2 ^ (l - 1)\<close>
    shows \<open>coeff_bound MLKEM_Q (snd (invntt_middle_loop_int (2^l - 1) (2^(8 - l)) j j cs))\<close>
using assms(5) proof (induct j)
  case 0
  show ?case using assms(1) by simp
next
  case (Suc j)
  define blen where
    \<open>blen = (2::nat) ^ (8 - l)\<close>
  define k0 where
    \<open>k0 = (2::nat) ^ l - 1\<close>
  define nb where
    \<open>nb = (2::nat) ^ (l - 1)\<close>
  define prev where
    \<open>prev = snd (invntt_middle_loop_int k0 blen j j cs)\<close>
  define z where
    \<open>z = zetas_int ! (k0 - j)\<close>
  have snoc: \<open>snd (invntt_middle_loop_int k0 blen (Suc j) (Suc j) cs) =
                invntt_inner_loop_int z (j * (2 * blen)) blen blen prev\<close>
    unfolding z_def prev_def by (rule invntt_middle_loop_int_snoc)
  from Suc.prems have j_le: \<open>j \<le> 2^(l-1)\<close>
    by simp
  hence ih: \<open>coeff_bound MLKEM_Q prev\<close>
    unfolding prev_def k0_def blen_def by (rule Suc.hyps)
  have len_prev: \<open>length prev = length cs\<close>
    unfolding prev_def k0_def blen_def by (rule invntt_middle_loop_int_length)
  have block_fits: \<open>j * (2 * blen) + 2 * blen \<le> length prev\<close>
  proof -
    have \<open>(l - 1) + (8 - l) = 7\<close>
      using assms(2,3) by simp
    hence \<open>(2::nat) ^ (l-1) * 2^(8-l) = 2^7\<close>
      by (metis power_add)
    hence nb_2blen: \<open>nb * (2 * blen) = 256\<close>
      unfolding nb_def blen_def by simp
    from Suc.prems have \<open>Suc j \<le> nb\<close>
      unfolding nb_def by simp
    hence \<open>Suc j * (2 * blen) \<le> nb * (2 * blen)\<close>
      by (rule mult_le_mono1)
    hence \<open>j * (2 * blen) + 2 * blen \<le> 256\<close>
      using nb_2blen by simp
    thus ?thesis
      using assms(4) len_prev by simp
  qed
  have z_bound: \<open>\<bar>z\<bar> \<le> 1659\<close>
  proof -
    have \<open>k0 < 128\<close>
    proof -
      have \<open>(2::nat)^l \<le> 2^7\<close>
        using assms(3) by (intro power_increasing) simp_all
      thus ?thesis
        unfolding k0_def by simp
    qed
    hence \<open>k0 - j < 128\<close>
      using diff_le_self le_less_trans by blast
    thus ?thesis
      unfolding z_def by (rule zetas_int_abs_bound)
  qed
  have \<open>coeff_bound MLKEM_Q (invntt_inner_loop_int z (j * (2 * blen)) blen blen prev)\<close>
    by (rule invntt_inner_loop_int_coeff_bound[OF ih block_fits le_refl z_bound])
  thus ?case
    unfolding k0_def[symmetric] blen_def[symmetric] using snoc by simp
qed

subsection \<open>Layer and Outer Loop\<close>

theorem invntt_layer_int_coeff_bound:
  assumes \<open>coeff_bound MLKEM_Q cs\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>length cs = MLKEM_N\<close>
    shows \<open>coeff_bound MLKEM_Q (invntt_layer_int l cs)\<close>
unfolding invntt_layer_int_def by (rule invntt_middle_loop_int_coeff_bound[OF assms]) simp

subsection \<open>Overflow Safety\<close>

text \<open>Overflow safety: if all coefficients are bounded by @{const MLKEM_Q}, sums and
  differences of two coefficients fit in 16-bit signed range.\<close>

lemma invntt_coeff_bound_sum_bounds:
  assumes \<open>coeff_bound MLKEM_Q cs\<close>
      and \<open>j < length cs\<close>
      and \<open>j + blen < length cs\<close>
    shows \<open>-32768 \<le> cs ! j + cs ! (j + blen)\<close>
      and \<open>cs ! j + cs ! (j + blen) \<le> 32767\<close>
      and \<open>-32768 \<le> cs ! (j + blen) - cs ! j\<close>
      and \<open>cs ! (j + blen) - cs ! j \<le> 32767\<close>
proof -
  from assms have j_bound: \<open>\<bar>cs ! j\<bar> < MLKEM_Q\<close>
      and jb_bound: \<open>\<bar>cs ! (j + blen)\<bar> < MLKEM_Q\<close>
    unfolding coeff_bound_def by auto
  show \<open>-32768 \<le> cs ! j + cs ! (j + blen)\<close>
      and \<open>cs ! j + cs ! (j + blen) \<le> 32767\<close>
      and \<open>-32768 \<le> cs ! (j + blen) - cs ! j\<close>
      and \<open>cs ! (j + blen) - cs ! j \<le> 32767\<close>
    using j_bound jb_bound by linarith+
qed

(*<*)
end
(*>*)
