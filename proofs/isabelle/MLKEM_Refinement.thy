(*<*)
theory MLKEM_Refinement
  imports MLKEM_Spec
begin
(*>*)

text \<open>
  Refinement between C word-level types and abstract integers.
  Defines the @{text refines_mlk_poly} predicate connecting concrete
  @{typ c_mlk_poly} values (16-bit signed word coefficients) to abstract
  @{typ int_poly} specifications, together with no-overflow conditions
  required for safe arithmetic.
\<close>

text_raw \<open>
\begin{figure}[ht]
\centering
\begin{tikzpicture}[>=Stealth, node distance=1.4cm and 4.5cm,
    box/.style={draw=mlkblue, fill=mlklightblue, rounded corners,
                minimum width=2.6cm, minimum height=0.8cm,
                align=center, font=\small},
    lbl/.style={font=\small\itshape, midway}]
  % Left column: C (word-level)
  \node[box] (cpre) {C pre-state\\[-1pt]\footnotesize\texttt{c\_mlk\_poly}};
  \node[box, below=of cpre] (cpost) {C post-state\\[-1pt]\footnotesize\texttt{c\_mlk\_poly}};
  % Right column: abstract (int-level)
  \node[box, right=of cpre] (apre) {Abstract pre-state\\[-1pt]\footnotesize\texttt{int\_poly}};
  \node[box, right=of cpost] (apost) {Abstract post-state\\[-1pt]\footnotesize\texttt{int\_poly}};
  % Vertical arrows: execution
  \draw[->,thick,mlkblue] (cpre) -- node[left,lbl] {C execution} (cpost);
  \draw[->,thick,mlkblue] (apre) -- node[right,lbl] {spec} (apost);
  % Horizontal arrows: refinement
  \draw[<->,densely dashed,thick,mlkblue] (cpre) --
    node[above,font=\small] {\textsf{refines}} (apre);
  \draw[<->,densely dashed,thick,mlkblue] (cpost) --
    node[below,font=\small] {\textsf{refines}} (apost);
\end{tikzpicture}
\caption{Refinement-based verification.  Each C function is executed in
  lockstep with its abstract specification.  The dashed arrows denote
  the refinement relation @{text refines_mlk_poly}, which requires that
  the signed interpretation of concrete 16-bit coefficients equals the
  abstract integer list.  A function contract establishes that if the
  refinement holds before execution (pre-state), it is preserved after
  execution (post-state).}
\label{fig:refinement}
\end{figure}
\<close>

section \<open>Concrete Types and Refinement\<close>

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

subsection \<open>Refinement Lemmas\<close>

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
theorem poly_add_c_refines:
  assumes \<open>refines_mlk_poly p ap\<close>
      and \<open>refines_mlk_poly q aq\<close>
      and \<open>no_overflow_add ap aq\<close>
    shows \<open>refines_mlk_poly (poly_add_c p q) (poly_add_int ap aq)\<close>
using assms by (auto simp add: c_mlk_poly.record_simps map2_map_map word_size refines_mlk_poly_def
  poly_add_c_def poly_add_int_def no_overflow_add_def intro!: nth_equalityI sint_plus_no_overflow)

subsection \<open>Auxiliary List Lemmas\<close>

lemma nth_map2:
  assumes \<open>i < length xs\<close>
      and \<open>i < length ys\<close>
    shows \<open>map2 f xs ys ! i = f (xs ! i) (ys ! i)\<close>
using assms by (induction xs arbitrary: i ys) (auto simp: less_Suc_eq_0_disj split: list.splits)

(*<*)
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

(*>*)

(*<*)
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
(*>*)

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

(*<*)
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
(*>*)

subsection \<open>Additional Refinement Predicates\<close>

definition refines_mlk_poly_mulcache :: \<open>c_mlk_poly_mulcache \<Rightarrow> int list \<Rightarrow> bool\<close> where
  \<open>refines_mlk_poly_mulcache cm am \<longleftrightarrow>
     length (c_mlk_poly_mulcache_coeffs cm) = 128 \<and>
     List.map sint (c_mlk_poly_mulcache_coeffs cm) = am\<close>

definition refines_coeffs :: \<open>c_short list \<Rightarrow> int list \<Rightarrow> bool\<close> where
  \<open>refines_coeffs ccs acs \<longleftrightarrow> length ccs = MLKEM_N \<and> List.map sint ccs = acs\<close>

lemma refines_mlk_poly_coeffs:
  shows \<open>refines_mlk_poly cp ap \<longleftrightarrow> refines_coeffs (c_mlk_poly_coeffs cp) ap\<close>
unfolding refines_mlk_poly_def refines_coeffs_def ..

(*<*)
end
(*>*)
