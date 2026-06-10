(*<*)
theory MLKEM_NTT_Spec
  imports MLKEM_Zetas
begin
(*>*)

text \<open>
  Abstract specification of the Number Theoretic Transform (NTT) matching
  the butterfly\,\<open>\<rightarrow>\<close>\,inner-loop\,\<open>\<rightarrow>\<close>\,middle-loop\,\<open>\<rightarrow>\<close>\,outer-loop
  structure of the C implementation. All operations on unbounded integers;
  overflow analysis is separate.
\<close>

section \<open>NTT Specification\<close>

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
  \node[io, right=4cm of a] (out1) {$a + \zeta \cdot b$};
  \node[io, right=4cm of b] (out2) {$a - \zeta \cdot b$};
  % Arrows
  \draw[->,thick,mlkblue] (a) -- (out1);
  \draw[->,thick,mlkblue] (a) -- (out2);
  \draw[->,thick,mlkblue] (b) -- node[above,pos=0.4] {$\times\,\zeta$} (out1);
  \draw[->,thick,mlkblue] (b) -- node[below,pos=0.4] {$\times\,(-\zeta)$} (out2);
\end{tikzpicture}
\caption{Forward NTT butterfly: given inputs $a$ and $b$ with twiddle
  factor $\zeta$, the outputs are $a + \mathit{fqmul}(b, \zeta)$ and
  $a - \mathit{fqmul}(b, \zeta)$, where \emph{fqmul} denotes
  Montgomery multiplication modulo~$q$.}
\label{fig:ntt-butterfly}
\end{figure}
\<close>

subsection \<open>Definitions\<close>

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

subsection \<open>Inner Loop Properties\<close>

(*<*)
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
  also have \<open>Suc off + m = off + Suc m\<close>
    by simp
  also have \<open>ntt_inner_loop_int z (Suc off) blen m (ntt_butterfly_int z off blen cs)
           = ntt_inner_loop_int z off blen (Suc m) cs\<close>
    by simp
  finally show ?case
    .
qed

lemma ntt_butterfly_int_nth_other:
  assumes \<open>i \<noteq> j\<close>
      and \<open>i \<noteq> j + blen\<close>
    shows \<open>ntt_butterfly_int zeta j blen cs ! i = cs ! i\<close>
unfolding ntt_butterfly_int_def Let_def using assms by simp

lemma ntt_inner_loop_int_nth_unchanged:
  assumes \<open>i \<notin> {off..<off+cnt}\<close>
      and \<open>i \<notin> {off+blen..<off+cnt+blen}\<close>
    shows \<open>ntt_inner_loop_int z off blen cnt cs ! i = cs ! i\<close>
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
  have \<open>ntt_inner_loop_int z off blen (Suc cnt) cs =
        ntt_inner_loop_int z (Suc off) blen cnt (ntt_butterfly_int z off blen cs)\<close>
    by simp
  hence \<open>ntt_inner_loop_int z off blen (Suc cnt) cs ! i =
         ntt_inner_loop_int z (Suc off) blen cnt (ntt_butterfly_int z off blen cs) ! i\<close>
    by simp
  also have \<open>\<dots> = (ntt_butterfly_int z off blen cs) ! i\<close>
    by (rule Suc.hyps[OF ih1 ih2])
  also have \<open>\<dots> = cs ! i\<close>
    by (rule ntt_butterfly_int_nth_other[OF \<open>i \<noteq> off\<close> \<open>i \<noteq> off + blen\<close>])
  finally show ?case
    .
qed

lemma ntt_inner_loop_int_low_val:
  assumes \<open>m < cnt\<close>
      and \<open>cnt \<le> blen\<close>
      and \<open>off + 2 * blen \<le> length cs\<close>
    shows \<open>ntt_inner_loop_int z off blen cnt cs ! (off + m) =
              cs ! (off + m) + fqmul_int (cs ! (off + m + blen)) z\<close>
using assms proof (induct cnt arbitrary: m)
  case 0
  then show ?case
    by simp
next
  case (Suc cnt)
  have snoc: \<open>ntt_inner_loop_int z off blen (Suc cnt) cs =
                ntt_butterfly_int z (off + cnt) blen (ntt_inner_loop_int z off blen cnt cs)\<close>
    by (rule ntt_inner_loop_int_snoc)
  define prev where \<open>prev = ntt_inner_loop_int z off blen cnt cs\<close>
  have len_prev: \<open>length prev = length cs\<close> unfolding prev_def
    by (rule ntt_inner_loop_int_length)
  have p1: \<open>prev ! (off + cnt) = cs ! (off + cnt)\<close>
    unfolding prev_def by (rule ntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  have p2: \<open>prev ! (off + cnt + blen) = cs ! (off + cnt + blen)\<close>
    unfolding prev_def by (rule ntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  show ?case
  proof (cases \<open>m = cnt\<close>)
    case True
    have \<open>off + cnt < length prev\<close>
      using Suc.prems len_prev by simp
    thus ?thesis using True snoc p1 p2
      by (simp add: ntt_butterfly_int_def Let_def prev_def[symmetric])
  next
    case False
    with Suc.prems have \<open>m < cnt\<close>
      by simp
    have \<open>off + m \<noteq> off + cnt\<close>
      using \<open>m < cnt\<close> by simp
    have \<open>off + m \<noteq> off + cnt + blen\<close>
      using \<open>m < cnt\<close> Suc.prems by simp
    have \<open>ntt_inner_loop_int z off blen (Suc cnt) cs ! (off + m) =
             prev ! (off + m)\<close>
      using snoc ntt_butterfly_int_nth_other[OF \<open>off + m \<noteq> off + cnt\<close> \<open>off + m \<noteq> off + cnt + blen\<close>]
        by (simp add: prev_def)
    also have \<open>\<dots> = cs ! (off + m) + fqmul_int (cs ! (off + m + blen)) z\<close>
      unfolding prev_def by (rule Suc.hyps[OF \<open>m < cnt\<close>]) (use Suc.prems in auto)
    finally show ?thesis
      .
  qed
qed

lemma ntt_inner_loop_int_high_val:
  assumes \<open>m < cnt\<close> \<open>cnt \<le> blen\<close> \<open>off + 2 * blen \<le> length cs\<close>
    shows \<open>ntt_inner_loop_int z off blen cnt cs ! (off + m + blen) =
           cs ! (off + m) - fqmul_int (cs ! (off + m + blen)) z\<close>
using assms proof (induct cnt arbitrary: m)
  case 0
  then show ?case
    by simp
next
  case (Suc cnt)
  have snoc: \<open>ntt_inner_loop_int z off blen (Suc cnt) cs =
                ntt_butterfly_int z (off + cnt) blen (ntt_inner_loop_int z off blen cnt cs)\<close>
    by (rule ntt_inner_loop_int_snoc)
  define prev where \<open>prev = ntt_inner_loop_int z off blen cnt cs\<close>
  have len_prev: \<open>length prev = length cs\<close>
    unfolding prev_def by (rule ntt_inner_loop_int_length)
  have p1: \<open>prev ! (off + cnt) = cs ! (off + cnt)\<close>
    unfolding prev_def by (rule ntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  have p2: \<open>prev ! (off + cnt + blen) = cs ! (off + cnt + blen)\<close>
    unfolding prev_def by (rule ntt_inner_loop_int_nth_unchanged) (use Suc.prems in auto)
  show ?case
  proof (cases \<open>m = cnt\<close>)
    case True
    have len1: \<open>off + cnt < length prev\<close>
      using Suc.prems len_prev by simp
    have len2: \<open>off + cnt + blen < length prev\<close>
      using Suc.prems len_prev by simp
    have ne: \<open>off + cnt + blen \<noteq> off + cnt\<close>
      using Suc.prems by simp
    thus ?thesis
      using True snoc p1 p2 ne len1 len2 by (simp add: ntt_butterfly_int_def Let_def prev_def[symmetric])
  next
    case False
    with Suc.prems have mc: \<open>m < cnt\<close>
      by simp
    have ne1: \<open>off + m + blen \<noteq> off + cnt\<close>
      using Suc.prems by simp
    have ne2: \<open>off + m + blen \<noteq> off + cnt + blen\<close>
      using mc by simp
    have \<open>ntt_inner_loop_int z off blen (Suc cnt) cs ! (off + m + blen) =
          prev ! (off + m + blen)\<close>
      using snoc ntt_butterfly_int_nth_other[OF ne1 ne2] by (simp add: prev_def)
    also have \<open>\<dots> = cs ! (off + m) - fqmul_int (cs ! (off + m + blen)) z\<close>
      unfolding prev_def by (rule Suc.hyps[OF \<open>m < cnt\<close>]) (use Suc.prems in auto)
    finally show ?thesis
      .
  qed
qed

(*>*)

subsection \<open>Coefficient Bounds and Overflow Predicates\<close>

text \<open>The NTT butterfly adds and subtracts values, so coefficient magnitudes
  grow with each layer.  To guarantee that intermediate results stay within
  the 16-bit machine word, we define a coefficient-bound predicate and a
  no-overflow predicate for individual butterfly steps.  The C verification
  uses these to thread overflow safety through all seven layers.\<close>

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
  \<open>ntt_layer_no_overflow l acs \<equiv>
    (let k0 = 2 ^ (l - 1); blen = 2 ^ (8 - l)
     in \<forall>j < 2 ^ (l - 1).
        ntt_inner_no_overflow (zetas_int ! (k0 + j)) (j * 2 * blen) blen blen
          (snd (ntt_middle_loop_int k0 blen j j acs)))\<close>

lemma ntt_layer_no_overflow_block:
  assumes \<open>ntt_layer_no_overflow l acs\<close> \<open>j < 2 ^ (l - 1)\<close>
  shows \<open>ntt_inner_no_overflow (zetas_int ! (2 ^ (l - 1) + j))
           (j * 2 * 2 ^ (8 - l)) (2 ^ (8 - l)) (2 ^ (8 - l))
           (snd (ntt_middle_loop_int (2 ^ (l - 1)) (2 ^ (8 - l)) j j acs))\<close>
using assms unfolding ntt_layer_no_overflow_def Let_def by auto

text \<open>Key fqmul bound: if the product is small enough,
  the Montgomery-reduced result is strictly less than Q.\<close>

lemma fqmul_int_bound_Q:
  assumes \<open>\<bar>a * b\<bar> < 32768 * MLKEM_Q\<close>
    shows \<open>\<bar>fqmul_int a b\<bar> < MLKEM_Q\<close>
proof -
  define t where \<open>t = signed_take_bit 15 ((a * b) mod 65536 * 62209 mod 65536)\<close>
  have result_eq: \<open>fqmul_int a b * 65536 = a * b - t * 3329\<close>
    unfolding fqmul_int_def t_def by (rule montgomery_reduce_int_result_eq)
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
  from assms have \<open>a * b < 32768 * 3329\<close> \<open>a * b > -(32768 * 3329)\<close>
    by (auto simp: abs_less_iff)
  have \<open>fqmul_int a b * 65536 < 65536 * 3329\<close>
    using result_eq \<open>a * b < _\<close> t_lb by linarith
  moreover have \<open>fqmul_int a b * 65536 > -(65536 * 3329)\<close>
    using result_eq \<open>a * b > _\<close> t_ub by linarith
  ultimately show ?thesis
    by simp
qed

(*<*)
subsection \<open>Middle Loop Properties\<close>

lemma ntt_middle_loop_int_fst:
  shows \<open>fst (ntt_middle_loop_int k blen rem nb cs) = k + rem\<close>
by (induct rem arbitrary: k cs) (auto simp: case_prod_beta Let_def)

lemma ntt_middle_loop_int_length:
  shows \<open>length (snd (ntt_middle_loop_int k blen rem nb cs)) = length cs\<close>
by (induct rem arbitrary: k cs) (auto simp: case_prod_beta Let_def ntt_inner_loop_int_length)

text \<open>Snoc decomposition for the middle loop: processing @{term \<open>Suc j\<close>} blocks
  equals processing @{term j} blocks then applying one more inner loop
  at the next block offset.\<close>

lemma ntt_middle_loop_int_snoc_gen:
  shows \<open>snd (ntt_middle_loop_int k blen (Suc j) (s + Suc j) cs) =
         ntt_inner_loop_int (zetas_int ! (k + j)) ((s + j) * (2 * blen)) blen blen
           (snd (ntt_middle_loop_int k blen j (s + j) cs))\<close>
proof (induct j arbitrary: k s cs)
  case 0
  then show ?case by (simp add: case_prod_beta Let_def)
next
  case (Suc j)
  \<comment> \<open>Unfold one step: processes block at offset s\<close>
  have lhs: \<open>ntt_middle_loop_int k blen (Suc (Suc j)) (s + Suc (Suc j)) cs =
        ntt_middle_loop_int (Suc k) blen (Suc j) (s + Suc (Suc j))
          (ntt_inner_loop_int (zetas_int ! k) (s * (2 * blen)) blen blen cs)\<close>
    by (simp add: case_prod_beta Let_def)
  define cs' where \<open>cs' = ntt_inner_loop_int (zetas_int ! k) (s * (2 * blen)) blen blen cs\<close>
  \<comment> \<open>Rewrite @{term \<open>s + Suc (Suc j)\<close>} = @{term \<open>Suc s + Suc j\<close>}\<close>
  have \<open>snd (ntt_middle_loop_int (Suc k) blen (Suc j) (Suc s + Suc j) cs') =
        ntt_inner_loop_int (zetas_int ! (Suc k + j)) ((Suc s + j) * (2 * blen)) blen blen
          (snd (ntt_middle_loop_int (Suc k) blen j (Suc s + j) cs'))\<close>
    by (rule Suc)
  \<comment> \<open>RHS unfolds the same way\<close>
  moreover have \<open>ntt_middle_loop_int k blen (Suc j) (s + Suc j) cs =
        ntt_middle_loop_int (Suc k) blen j (s + Suc j)
          (ntt_inner_loop_int (zetas_int ! k) (s * (2 * blen)) blen blen cs)\<close>
    by (simp add: case_prod_beta Let_def)
  ultimately show ?case
    using lhs by (simp add: cs'_def)
qed

corollary ntt_middle_loop_int_snoc:
  shows \<open>snd (ntt_middle_loop_int k blen (Suc j) (Suc j) cs) =
         ntt_inner_loop_int (zetas_int ! (k + j)) (j * (2 * blen)) blen blen
           (snd (ntt_middle_loop_int k blen j j cs))\<close>
using ntt_middle_loop_int_snoc_gen[where s=0] by simp

(*>*)

subsection \<open>Bound Propagation Through NTT Layers\<close>

lemma coeff_bound_mono:
  assumes \<open>coeff_bound B cs\<close> \<open>B \<le> B'\<close>
  shows \<open>coeff_bound B' cs\<close>
using assms unfolding coeff_bound_def by (meson order_less_le_trans)

lemma ntt_middle_loop_int_nth_unchanged:
  assumes \<open>j * (2 * blen) \<le> i\<close>
  shows \<open>snd (ntt_middle_loop_int k blen j j cs) ! i = cs ! i\<close>
using assms proof (induct j arbitrary: k cs)
  case 0
  then show ?case
    by simp
next
  case (Suc j)
  have snoc: \<open>snd (ntt_middle_loop_int k blen (Suc j) (Suc j) cs) =
    ntt_inner_loop_int (zetas_int ! (k + j)) (j * (2 * blen)) blen blen
      (snd (ntt_middle_loop_int k blen j j cs))\<close>
    by (rule ntt_middle_loop_int_snoc)
  define prev where \<open>prev = snd (ntt_middle_loop_int k blen j j cs)\<close>
  from Suc.prems have \<open>j * (2 * blen) \<le> i\<close>
    by simp
  hence ih: \<open>prev ! i = cs ! i\<close>
    unfolding prev_def by (rule Suc.hyps)
  from Suc.prems have \<open>i \<notin> {j * (2 * blen)..<j * (2 * blen) + blen}\<close>
    by auto
  moreover from Suc.prems have \<open>i \<notin> {j * (2 * blen) + blen..<j * (2 * blen) + blen + blen}\<close>
    by auto
  ultimately have \<open>ntt_inner_loop_int (zetas_int ! (k + j)) (j * (2 * blen)) blen blen prev ! i = prev ! i\<close>
    by (rule ntt_inner_loop_int_nth_unchanged)
  with ih snoc show ?case
    by (simp add: prev_def)
qed

lemma ntt_middle_loop_int_coeff_bound:
  assumes cb: \<open>coeff_bound (int l * MLKEM_Q) cs\<close>
      and l_ge: \<open>1 \<le> l\<close>
      and l_le: \<open>l \<le> 7\<close>
      and len: \<open>length cs = MLKEM_N\<close>
      and j_le: \<open>j \<le> 2 ^ (l - 1)\<close>
    shows \<open>coeff_bound (int (l + 1) * MLKEM_Q)
             (snd (ntt_middle_loop_int (2^(l-1)) (2^(8-l)) j j cs))\<close>
using j_le proof (induct j)
  case 0
  show ?case
    using coeff_bound_mono[OF cb] by simp
next
  case (Suc j)
  define blen where \<open>blen = (2::nat) ^ (8 - l)\<close>
  define k0 where \<open>k0 = (2::nat) ^ (l - 1)\<close>
  define prev where \<open>prev = snd (ntt_middle_loop_int k0 blen j j cs)\<close>
  define z where \<open>z = zetas_int ! (k0 + j)\<close>
  have snoc: \<open>snd (ntt_middle_loop_int k0 blen (Suc j) (Suc j) cs) =
                ntt_inner_loop_int z (j * (2 * blen)) blen blen prev\<close>
    unfolding z_def prev_def by (rule ntt_middle_loop_int_snoc)
  from Suc.prems have \<open>j \<le> 2^(l-1)\<close>
    by simp
  hence ih: \<open>coeff_bound (int (l + 1) * MLKEM_Q) prev\<close>
    unfolding prev_def k0_def blen_def by (rule Suc.hyps)
  have len_prev: \<open>length prev = length cs\<close>
    unfolding prev_def k0_def blen_def by (rule ntt_middle_loop_int_length)
  have block_fits: \<open>j * (2 * blen) + 2 * blen \<le> length cs\<close>
  proof -
    have k0_2blen: \<open>k0 * (2 * blen) = 256\<close>
    proof -
      have \<open>l - 1 + (8 - l) = 7\<close>
        using l_ge l_le by simp
      hence \<open>(2::nat) ^ (l - 1) * 2 ^ (8 - l) = 2 ^ 7\<close>
        by (metis power_add)
      thus ?thesis
        unfolding k0_def blen_def by simp
    qed
    from Suc.prems have \<open>Suc j \<le> k0\<close>
      unfolding k0_def by simp
    hence \<open>Suc j * (2 * blen) \<le> k0 * (2 * blen)\<close>
      by (intro mult_le_mono1)
    thus ?thesis
      using k0_2blen len by simp
  qed
  have z_bound: \<open>\<bar>z\<bar> \<le> 1659\<close>
  proof -
    have \<open>k0 + j < 128\<close>
    proof -
      have \<open>2 * k0 \<le> 128\<close>
      proof -
        have \<open>l - 1 \<le> 6\<close>
          using l_le by simp
        hence \<open>(2::nat) ^ (l - 1) \<le> 2 ^ 6\<close>
          by (intro power_increasing) simp_all
        thus ?thesis
          unfolding k0_def by simp
      qed
      moreover from Suc.prems have \<open>j < k0\<close>
        unfolding k0_def by simp
      ultimately show ?thesis
        by simp
    qed
    thus ?thesis
      unfolding z_def by (rule zetas_int_abs_bound)
  qed
  show ?case unfolding snoc k0_def[symmetric] blen_def[symmetric]
    unfolding coeff_bound_def ntt_inner_loop_int_length len_prev
  proof (intro allI impI)
    fix i assume i_lt: \<open>i < length cs\<close>
    have fqmul_bound: \<open>\<bar>fqmul_int x z\<bar> < MLKEM_Q\<close> if \<open>\<bar>x\<bar> < int l * MLKEM_Q\<close> for x
    proof (rule fqmul_int_bound_Q)
      have \<open>\<bar>x * z\<bar> = \<bar>x\<bar> * \<bar>z\<bar>\<close>
        by (rule abs_mult)
      also have \<open>\<dots> \<le> (int l * 3329 - 1) * 1659\<close>
      proof (rule mult_mono)
        from that show \<open>\<bar>x\<bar> \<le> int l * 3329 - 1\<close>
          by linarith
      qed (use z_bound l_ge in auto)
      also have \<open>\<dots> < 32768 * 3329\<close>
        using l_ge l_le by simp
      finally show \<open>\<bar>x * z\<bar> < 32768 * MLKEM_Q\<close>
        by simp
    qed
    show \<open>\<bar>ntt_inner_loop_int z (j * (2 * blen)) blen blen prev ! i\<bar> < int (l + 1) * MLKEM_Q\<close>
    proof (cases \<open>j * (2 * blen) \<le> i \<and> i < j * (2 * blen) + blen\<close>)
      case True
      then obtain m where i_eq: \<open>i = j * (2 * blen) + m\<close> and m_lt: \<open>m < blen\<close>
        by (metis le_add_diff_inverse nat_add_left_cancel_less)
      have \<open>ntt_inner_loop_int z (j * (2 * blen)) blen blen prev ! i =
           prev ! i + fqmul_int (prev ! (i + blen)) z\<close>
        unfolding i_eq by (rule ntt_inner_loop_int_low_val[OF m_lt le_refl]) (use block_fits len_prev in simp)
      also have \<open>prev ! i = cs ! i\<close>
        unfolding prev_def by (rule ntt_middle_loop_int_nth_unchanged) (use True in simp)
      also have \<open>prev ! (i + blen) = cs ! (i + blen)\<close>
        unfolding prev_def by (rule ntt_middle_loop_int_nth_unchanged) (use True in simp)
      finally have val: \<open>ntt_inner_loop_int z (j * (2 * blen)) blen blen prev ! i =
        cs ! i + fqmul_int (cs ! (i + blen)) z\<close> .
      have ci: \<open>\<bar>cs ! i\<bar> < int l * MLKEM_Q\<close>
        using cb i_lt unfolding coeff_bound_def by auto
      have cib: \<open>\<bar>cs ! (i + blen)\<bar> < int l * MLKEM_Q\<close>
        using cb block_fits True unfolding coeff_bound_def blen_def by auto
      have int_expand: \<open>int (l + 1) * MLKEM_Q = int l * MLKEM_Q + MLKEM_Q\<close>
        by (simp add: algebra_simps)
      show ?thesis unfolding val int_expand
        using ci fqmul_bound[OF cib] abs_triangle_ineq[of \<open>cs!i\<close> \<open>fqmul_int (cs!(i+blen)) z\<close>] by linarith
    next
      case False
      show ?thesis
      proof (cases \<open>j * (2 * blen) + blen \<le> i \<and> i < j * (2 * blen) + 2 * blen\<close>)
        case True
        then obtain m where i_eq: \<open>i = j * (2 * blen) + m + blen\<close> and m_lt: \<open>m < blen\<close>
          by (metis add.commute group_cancel.add1 le_add_diff_inverse left_add_twice nat_add_left_cancel_less)
        have \<open>ntt_inner_loop_int z (j * (2 * blen)) blen blen prev ! i =
             prev ! (j * (2 * blen) + m) - fqmul_int (prev ! i) z\<close>
          unfolding i_eq by (rule ntt_inner_loop_int_high_val[OF m_lt le_refl]) (use block_fits len_prev in simp)
        also have \<open>prev ! (j * (2 * blen) + m) = cs ! (j * (2 * blen) + m)\<close>
          unfolding prev_def by (rule ntt_middle_loop_int_nth_unchanged) simp
        also have \<open>prev ! i = cs ! i\<close>
          unfolding prev_def by (rule ntt_middle_loop_int_nth_unchanged) (use True in simp)
        finally have val: \<open>ntt_inner_loop_int z (j * (2 * blen)) blen blen prev ! i =
                      cs ! (j * (2 * blen) + m) - fqmul_int (cs ! i) z\<close>
          .
        have ci: \<open>\<bar>cs ! (j * (2 * blen) + m)\<bar> < int l * MLKEM_Q\<close>
          using cb block_fits m_lt unfolding coeff_bound_def by auto
        have cib: \<open>\<bar>cs ! i\<bar> < int l * MLKEM_Q\<close>
          using cb i_lt unfolding coeff_bound_def by auto
        have int_expand: \<open>int (l + 1) * MLKEM_Q = int l * MLKEM_Q + MLKEM_Q\<close>
          by (simp add: algebra_simps)
        show ?thesis unfolding val int_expand
          using ci fqmul_bound[OF cib]
            abs_triangle_ineq[of \<open>cs!(j*(2*blen)+m)\<close> \<open>- fqmul_int (cs!i) z\<close>] by linarith
      next
        case False
        with \<open>\<not> (j * (2 * blen) \<le> i \<and> i < j * (2 * blen) + blen)\<close>
        have \<open>i \<notin> {j * (2 * blen)..<j * (2 * blen) + blen}\<close>
             \<open>i \<notin> {j * (2 * blen) + blen..<j * (2 * blen) + blen + blen}\<close>
          by auto
        hence \<open>ntt_inner_loop_int z (j * (2 * blen)) blen blen prev ! i = prev ! i\<close>
          by (rule ntt_inner_loop_int_nth_unchanged)
        moreover have \<open>\<bar>prev ! i\<bar> < int (l + 1) * MLKEM_Q\<close>
          using ih i_lt len_prev unfolding coeff_bound_def by auto
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
qed

theorem ntt_layer_int_bound:
  assumes \<open>coeff_bound (int l * MLKEM_Q) cs\<close>
      and \<open>1 \<le> l\<close>
      and \<open>l \<le> 7\<close>
      and \<open>length cs = MLKEM_N\<close>
    shows \<open>coeff_bound (int (l + 1) * MLKEM_Q) (ntt_layer_int l cs)\<close>
unfolding ntt_layer_int_def by (rule ntt_middle_loop_int_coeff_bound[OF assms]) simp

(*<*)
lemma ntt_layer_int_length:
  shows \<open>length (ntt_layer_int l cs) = length cs\<close>
unfolding ntt_layer_int_def by (rule ntt_middle_loop_int_length)

lemma ntt_outer_loop_int_length:
  shows \<open>length (ntt_outer_loop_int k n cs) = length cs\<close>
by (induction n arbitrary: k cs) (auto simp: case_prod_beta Let_def ntt_middle_loop_int_length)
(*>*)

lemma ntt_outer_loop_int_bound:
  assumes \<open>coeff_bound (int l * MLKEM_Q) cs\<close>
      and \<open>1 \<le> l\<close> and \<open>l + lr = 8\<close>
      and \<open>length cs = MLKEM_N\<close>
      and \<open>k = 2^(l-1)\<close>
  shows \<open>coeff_bound (int (l + lr) * MLKEM_Q) (ntt_outer_loop_int k lr cs)\<close>
using assms proof (induct lr arbitrary: l k cs)
  case 0
  then show ?case
    by simp
next
  case (Suc lr)
  define blen where \<open>blen = (2::nat) ^ Suc lr\<close>
  define nb where \<open>nb = (2::nat) ^ (6 - lr)\<close>
  obtain k' cs' where mid: \<open>ntt_middle_loop_int k blen nb nb cs = (k', cs')\<close>
    by (cases \<open>ntt_middle_loop_int k blen nb nb cs\<close>)
  have cs'_eq: \<open>cs' = snd (ntt_middle_loop_int k blen nb nb cs)\<close>
    using mid by simp
  have k'_eq: \<open>k' = k + nb\<close>
    using ntt_middle_loop_int_fst[of k blen nb nb cs] mid by simp
  have len_cs': \<open>length cs' = MLKEM_N\<close>
    using cs'_eq ntt_middle_loop_int_length[of k blen nb nb cs] Suc.prems(4) by simp
  have l_eq: \<open>Suc lr = 8 - l\<close>
    using Suc.prems(2,3) by simp
  have exp_eq: \<open>6 - lr = l - 1\<close>
  proof -
    from l_eq Suc.prems(2) have \<open>l - 1 + lr = 6\<close>
      by simp
    thus ?thesis
      by simp
  qed
  have nb_eq: \<open>nb = 2^(l - 1)\<close>
    unfolding nb_def using exp_eq by simp
  have blen_eq: \<open>blen = 2^(8-l)\<close>
    unfolding blen_def using l_eq by simp
  have k_eq: \<open>k = 2^(l-1)\<close>
    using Suc.prems(5) .
  have cb': \<open>coeff_bound (int (l+1) * MLKEM_Q) cs'\<close>
    unfolding cs'_eq blen_eq nb_eq k_eq by (rule ntt_middle_loop_int_coeff_bound[OF Suc.prems(1,2)])
      (use Suc.prems in simp_all)
  have k'_val: \<open>k' = 2 ^ l\<close>
  proof -
    have \<open>Suc (l - 1) = l\<close>
      using Suc.prems(2) by simp
    thus ?thesis
      unfolding k'_eq k_eq nb_eq by (metis power_Suc mult_2)
  qed
  have unroll: \<open>ntt_outer_loop_int k (Suc lr) cs =
    ntt_outer_loop_int k' lr cs'\<close>
    by (simp only: ntt_outer_loop_int.simps blen_def[symmetric] nb_def[symmetric]
        Let_def case_prod_beta mid prod.sel)
  show ?case unfolding unroll
    apply (subst add_Suc_right)
    apply (subst add_Suc[symmetric])
    apply (rule Suc.hyps)
    apply (use cb' Suc.prems k'_val len_cs' in simp_all)
    done
qed

lemma poly_ntt_int_bound:
  assumes \<open>coeff_bound MLKEM_Q cs\<close>
      and \<open>length cs = MLKEM_N\<close>
    shows \<open>coeff_bound (8 * MLKEM_Q) (poly_ntt_int cs)\<close>
proof -
  have \<open>coeff_bound (int 1 * MLKEM_Q) cs\<close>
    using assms(1) by simp
  hence \<open>coeff_bound (int (1 + 7) * MLKEM_Q) (ntt_outer_loop_int (2^(1-1)) 7 cs)\<close>
    by (rule ntt_outer_loop_int_bound) (use assms(2) in simp_all)
  thus ?thesis
    unfolding poly_ntt_int_def by simp
qed

subsection \<open>No-Overflow From Coefficient Bounds\<close>

text \<open>Coefficient bound implies no overflow for one NTT layer.
  If all coefficients are bounded by @{term \<open>l * Q\<close>} with @{term \<open>l \<le> 7\<close>},
  then each butterfly in the layer produces values in 16-bit range.\<close>

theorem coeff_bound_implies_ntt_layer_no_overflow:
  assumes cb: \<open>coeff_bound (int l * MLKEM_Q) acs\<close>
      and l_ge: \<open>1 \<le> l\<close>
      and l_le: \<open>l \<le> 7\<close>
      and len: \<open>length acs = MLKEM_N\<close>
    shows \<open>ntt_layer_no_overflow l acs\<close>
proof -
  define k0 where \<open>k0 = (2::nat) ^ (l - 1)\<close>
  define blen where \<open>blen = (2::nat) ^ (8 - l)\<close>
  have k0_2blen: \<open>k0 * (2 * blen) = 256\<close>
  proof -
    have \<open>l - 1 + (8 - l) = 7\<close>
      using l_ge l_le by simp
    hence \<open>(2::nat) ^ (l - 1) * 2 ^ (8 - l) = 2 ^ 7\<close>
      by (metis power_add)
    thus ?thesis
      unfolding k0_def blen_def by simp
  qed
  have inner: \<open>ntt_inner_no_overflow (zetas_int ! (k0 + j)) (j * 2 * blen) blen blen
                (snd (ntt_middle_loop_int k0 blen j j acs))\<close>
    if j_lt: \<open>j < k0\<close> for j
  proof -
    define zeta where \<open>zeta = zetas_int ! (k0 + j)\<close>
    define off where \<open>off = j * 2 * blen\<close>
    define prev where \<open>prev = snd (ntt_middle_loop_int k0 blen j j acs)\<close>
    have block_fits: \<open>off + 2 * blen \<le> 256\<close>
    proof -
      from j_lt have \<open>(j + 1) * (2 * blen) \<le> k0 * (2 * blen)\<close>
        by (intro mult_le_mono1) simp
      thus ?thesis
        using k0_2blen unfolding off_def by (simp add: algebra_simps)
    qed
    have z_bound: \<open>\<bar>zeta\<bar> \<le> 1659\<close>
    proof -
      have \<open>k0 + j < 128\<close>
      proof -
        have \<open>2 * k0 \<le> 128\<close>
        proof -
          have \<open>l - 1 \<le> 6\<close>
            using l_le by simp
          hence \<open>(2::nat) ^ (l - 1) \<le> 2 ^ 6\<close>
            by (intro power_increasing) simp_all
          thus ?thesis
            unfolding k0_def by simp
        qed
        with j_lt show ?thesis
          by simp
      qed
      thus ?thesis
        unfolding zeta_def by (rule zetas_int_abs_bound)
    qed
    have fqmul_bound: \<open>\<bar>fqmul_int x zeta\<bar> < MLKEM_Q\<close> if \<open>\<bar>x\<bar> < int l * MLKEM_Q\<close> for x
    proof (rule fqmul_int_bound_Q)
      have \<open>\<bar>x * zeta\<bar> = \<bar>x\<bar> * \<bar>zeta\<bar>\<close>
        by (rule abs_mult)
      also have \<open>\<dots> \<le> (int l * 3329 - 1) * 1659\<close>
      proof (rule mult_mono)
        from that show \<open>\<bar>x\<bar> \<le> int l * 3329 - 1\<close>
          by linarith
      qed (use z_bound l_ge in auto)
      also have \<open>\<dots> < 32768 * 3329\<close>
        using l_ge l_le by simp
      finally show \<open>\<bar>x * zeta\<bar> < 32768 * MLKEM_Q\<close>
        by simp
    qed
    show ?thesis
      unfolding ntt_inner_no_overflow_def Let_def zeta_def[symmetric]
        off_def[symmetric] prev_def[symmetric]
    proof (intro allI impI conjI)
         fix m
      assume m_lt: \<open>m < blen\<close>
      define cs' where \<open>cs' = ntt_inner_loop_int zeta off blen m prev\<close>
      define idx where \<open>idx = off + m\<close>
      \<comment> \<open>Positions are unchanged by inner loop (not yet processed)\<close>
      have cs'_idx: \<open>cs' ! idx = prev ! idx\<close>
        unfolding cs'_def idx_def
        by (rule ntt_inner_loop_int_nth_unchanged) (use m_lt in auto)
      have cs'_idx_blen: \<open>cs' ! (idx + blen) = prev ! (idx + blen)\<close>
        unfolding cs'_def idx_def
        by (rule ntt_inner_loop_int_nth_unchanged) (use m_lt in auto)
      \<comment> \<open>Positions are unchanged by middle loop (in later block)\<close>
      have prev_idx: \<open>prev ! idx = acs ! idx\<close>
        unfolding prev_def k0_def blen_def idx_def off_def
        by (rule ntt_middle_loop_int_nth_unchanged) simp
      have prev_idx_blen: \<open>prev ! (idx + blen) = acs ! (idx + blen)\<close>
        unfolding prev_def k0_def blen_def idx_def off_def
        by (rule ntt_middle_loop_int_nth_unchanged) simp
      \<comment> \<open>Index bounds\<close>
      have idx_lt: \<open>idx < 256\<close>
        using m_lt block_fits unfolding idx_def by simp
      have idx_blen_lt: \<open>idx + blen < 256\<close>
        using m_lt block_fits unfolding idx_def by simp
      \<comment> \<open>Original values are bounded\<close>
      have cb_idx: \<open>\<bar>acs ! idx\<bar> < int l * MLKEM_Q\<close>
        using cb idx_lt len unfolding coeff_bound_def by auto
      have cb_idx_blen: \<open>\<bar>acs ! (idx + blen)\<bar> < int l * MLKEM_Q\<close>
        using cb idx_blen_lt len unfolding coeff_bound_def by auto
      \<comment> \<open>The fqmul result\<close>
      define t where \<open>t = fqmul_int (acs ! (idx + blen)) zeta\<close>
      have t_eq: \<open>fqmul_int (cs' ! (idx + blen)) zeta = t\<close>
        using cs'_idx_blen prev_idx_blen unfolding t_def by simp
      have t_bound: \<open>\<bar>t\<bar> < MLKEM_Q\<close>
        unfolding t_def by (rule fqmul_bound[OF cb_idx_blen])
      \<comment> \<open>Range bounds\<close>
      have range: \<open>(int l + 1) * MLKEM_Q \<le> 32768\<close>
        using l_le by simp
      have val_idx: \<open>cs' ! idx = acs ! idx\<close>
        using cs'_idx prev_idx by simp
      have plus_bound: \<open>\<bar>acs ! idx + t\<bar> < (int l + 1) * MLKEM_Q\<close>
      proof -
        have \<open>\<bar>acs ! idx + t\<bar> \<le> \<bar>acs ! idx\<bar> + \<bar>t\<bar>\<close>
          by (rule abs_triangle_ineq)
        also have \<open>\<dots> < int l * MLKEM_Q + MLKEM_Q\<close>
          using cb_idx t_bound by linarith
        finally show ?thesis
          by (simp add: ring_distribs)
      qed
      have minus_bound: \<open>\<bar>acs ! idx - t\<bar> < (int l + 1) * MLKEM_Q\<close>
      proof -
        have \<open>\<bar>acs ! idx - t\<bar> \<le> \<bar>acs ! idx\<bar> + \<bar>t\<bar>\<close>
          using abs_triangle_ineq[of \<open>acs ! idx\<close> \<open>-t\<close>] by simp
        also have \<open>\<dots> < int l * MLKEM_Q + MLKEM_Q\<close>
          using cb_idx t_bound by linarith
        finally show ?thesis
          by (simp add: ring_distribs)
      qed
      show \<open>- 32768 \<le> ntt_inner_loop_int zeta off blen m prev ! (off + m) +
              fqmul_int (ntt_inner_loop_int zeta off blen m prev ! (off + m + blen)) zeta\<close>
        using plus_bound range val_idx t_eq unfolding cs'_def idx_def by linarith
      show \<open>ntt_inner_loop_int zeta off blen m prev ! (off + m) +
              fqmul_int (ntt_inner_loop_int zeta off blen m prev ! (off + m + blen)) zeta \<le> 32767\<close>
        using plus_bound range val_idx t_eq unfolding cs'_def idx_def by linarith
      show \<open>- 32768 \<le> ntt_inner_loop_int zeta off blen m prev ! (off + m) -
              fqmul_int (ntt_inner_loop_int zeta off blen m prev ! (off + m + blen)) zeta\<close>
        using minus_bound range val_idx t_eq unfolding cs'_def idx_def by linarith
      show \<open>ntt_inner_loop_int zeta off blen m prev ! (off + m) -
              fqmul_int (ntt_inner_loop_int zeta off blen m prev ! (off + m + blen)) zeta \<le> 32767\<close>
        using minus_bound range val_idx t_eq unfolding cs'_def idx_def by linarith
    qed
  qed
  thus ?thesis
    unfolding ntt_layer_no_overflow_def Let_def
      k0_def[symmetric] blen_def[symmetric] by auto
qed

subsection \<open>Outer Loop Composition\<close>

text \<open>Outer loop layer composition.\<close>

lemma ntt_outer_loop_int_layer:
  assumes \<open>layer_rem \<le> 7\<close>
    shows \<open>ntt_outer_loop_int k (Suc layer_rem) cs =
             (let blen      = 2 ^ (Suc layer_rem);
                  nb        = 2 ^ (6 - layer_rem);
                  (k', cs') = ntt_middle_loop_int k blen nb nb cs
               in ntt_outer_loop_int k' layer_rem cs')\<close>
by simp

text \<open>Stepping the outer loop: one layer via @{const ntt_layer_int}.\<close>

lemma ntt_outer_loop_step_layer:
  assumes \<open>1 \<le> l\<close> \<open>l \<le> 7\<close>
  shows \<open>ntt_outer_loop_int (2^(l-1)) (8-l) cs =
         ntt_outer_loop_int (2^l) (7-l) (ntt_layer_int l cs)\<close>
proof -
  define blen where \<open>blen = (2::nat) ^ Suc (7 - l)\<close>
  define nb where \<open>nb = (2::nat) ^ (6 - (7 - l))\<close>
  from assms have sl: \<open>8 - l = Suc (7 - l)\<close>
    by simp
  from assms have exp_eq: \<open>6 - (7 - l) = l - 1\<close>
    by simp
  obtain k' cs' where mid: \<open>ntt_middle_loop_int (2^(l-1)) blen nb nb cs = (k', cs')\<close>
    by (cases \<open>ntt_middle_loop_int (2^(l-1)) blen nb nb cs\<close>)
  have nb_eq: \<open>nb = 2^(l-1)\<close>
    unfolding nb_def using exp_eq by simp
  have blen_eq: \<open>blen = 2^(8-l)\<close>
    unfolding blen_def using sl by simp
  have cs'_eq: \<open>cs' = ntt_layer_int l cs\<close>
    using mid unfolding ntt_layer_int_def nb_eq blen_eq by simp
  have k'_eq: \<open>k' = 2^l\<close>
  proof -
    have \<open>k' = 2^(l-1) + 2^(l-1)\<close>
      using ntt_middle_loop_int_fst[of \<open>2^(l-1)\<close> blen nb nb cs] mid nb_eq by simp
    thus ?thesis using assms(1)
      by (simp add: mult_2[symmetric] power_Suc[symmetric])
  qed
  show ?thesis
    unfolding sl by (simp only: ntt_outer_loop_int.simps blen_def[symmetric] nb_def[symmetric]
        Let_def case_prod_beta mid prod.sel k'_eq cs'_eq)
qed

(*<*)
end
(*>*)
