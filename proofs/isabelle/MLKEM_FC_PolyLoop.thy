(*<*)
theory MLKEM_FC_PolyLoop
  imports MLKEM_FC_Montgomery MLKEM_Zetas
begin
(*>*)

text \<open>
  Functional correctness proofs for polynomial loop operations:
  Montgomery pre-scaling (@{verbatim \<open>mlk_poly_tomont\<close>}), Barrett
  reduction (@{verbatim \<open>mlk_poly_reduce\<close>}), and mulcache computation
  (@{verbatim \<open>mlk_poly_mulcache_compute\<close>}).
\<close>

section \<open>Polynomial Loop Operations\<close>

(*<*)
context c_mlk_machine_model
begin

declare c_mlk_poly_mulcache_compute_c_def [micro_rust_simps del]
declare c_mlk_poly_reduce_c_def [micro_rust_simps del]
declare c_global_mlk_zetas_def [micro_rust_simps del]
(*>*)

subsection \<open>@{text mlk_poly_tomont_c} contract\<close>

text \<open>Montgomery-domain conversion loop.  Each coefficient is multiplied
  by the constant 1353 via @{verbatim \<open>fqmul\<close>}, mapping the polynomial
  into Montgomery representation.\<close>

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
(*<*)ucincl_auto c_mlk_poly_tomont_c_contract(*>*)

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

subsection \<open>@{text mlk_poly_tomont} contract\<close>

text \<open>Top-level wrapper: delegates to the inner loop via the
  @{const refines_mlk_poly} abstraction boundary.\<close>

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
(*<*)ucincl_auto c_mlk_poly_tomont_contract(*>*)

declare c_mlk_poly_tomont_c_def [micro_rust_simps del]

lemma c_mlk_poly_tomont_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_tomont MLKEM_N while_fuel while_fuel r \<Turnstile>\<^sub>F
            c_mlk_poly_tomont_contract r gr vr ar\<close>
  apply (crush_boot f: c_mlk_poly_tomont_def contract: c_mlk_poly_tomont_contract_def)
  apply (rule wp_callI[OF c_mlk_poly_tomont_c_spec[where gr=gr and vr=vr and ar=ar]])
  apply (simp add: c_mlk_poly_tomont_c_contract_def)
  apply (crush_base simp add: c_mlk_poly_tomont_c_contract_def)
  done

subsection \<open>@{text mlk_poly_reduce_c} contract\<close>

text \<open>Barrett reduction loop.  Applies @{const barrett_reduce_int} to every
  coefficient, bringing each into a centered representative modulo @{const MLKEM_Q}.\<close>

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
(*<*)ucincl_auto c_mlk_poly_reduce_c_contract(*>*)

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
  apply (auto intro!: nth_equalityI intro: barrett_reduce_int_in_range simp add: barrett_reduce_mod)
  done

subsection \<open>@{text mlk_poly_reduce} contract\<close>

text \<open>Top-level Barrett reduction wrapper, lifting the coefficient-level
  loop through the @{const refines_mlk_poly} abstraction.\<close>

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
(*<*)ucincl_auto c_mlk_poly_reduce_contract(*>*)

lemma c_mlk_poly_reduce_spec [crush_specs]:
  shows \<open>\<Gamma>; c_mlk_poly_reduce MLKEM_N while_fuel while_fuel r \<Turnstile>\<^sub>F
            c_mlk_poly_reduce_contract r gr vr ar\<close>
  apply (crush_boot f: c_mlk_poly_reduce_def contract: c_mlk_poly_reduce_contract_def)
  apply (rule wp_callI[OF c_mlk_poly_reduce_c_spec[where gr=gr and vr=vr and ar=ar]])
  apply (simp add: c_mlk_poly_reduce_c_contract_def)
  apply (crush_base simp add: c_mlk_poly_reduce_c_contract_def)
  done

subsection \<open>@{text mlk_poly_mulcache_compute_c} contract\<close>

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
(*<*)ucincl_auto c_mlk_poly_mulcache_compute_c_contract(*>*)

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

subsection \<open>@{text mlk_poly_mulcache_compute} contract\<close>

text \<open>Top-level wrapper for the multiplication-cache computation,
  lifting the inner loop through the poly abstraction.\<close>

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
(*<*)ucincl_auto c_mlk_poly_mulcache_compute_contract(*>*)

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

(*<*)
end
(*>*)

(*<*)
end
(*>*)
