theory MLKEM_Machine_Model_Instance
  imports
    MLKEM_Machine_Model
    "Micro_Rust_Runtime.Runtime_Heap"
    "Shallow_Micro_C.C_Byte_Encoding"
begin

section \<open>Consistency model for @{locale c_mlk_machine_model}\<close>

subsection \<open>Default instance for byte lists\<close>

text \<open>
  The heap model @{type mem} requires @{class default} on the stored value type.
  We instantiate it for lists with the empty list as default value.
\<close>

instantiation list :: (type) default
begin

definition default_list :: \<open>'a list\<close> where
  \<open>default_list = []\<close>

instance ..

end

text \<open>
  We provide a concrete interpretation of the @{locale c_mlk_machine_model} locale
  using the AutoCorrode heap model from @{theory Micro_Rust_Runtime.Runtime_Heap},
  together with byte-level prisms for all C types.
  The successful processing of this theory proves that the locale assumptions
  are consistent (satisfiable).
\<close>

subsection \<open>Byte prism for @{type c_short} lists\<close>

fun decode_c_short_list :: \<open>8 word list \<Rightarrow> c_short list option\<close> where
  \<open>decode_c_short_list [] = Some []\<close>
| \<open>decode_c_short_list [_] = None\<close>
| \<open>decode_c_short_list (a # b # rest) =
    Option.bind (prism_project c_short_byte_prism [a, b])
      (\<lambda>c. map_option ((#) c) (decode_c_short_list rest))\<close>

definition c_short_list_byte_prism :: \<open>(8 word list, c_short list) prism\<close> where
  \<open>c_short_list_byte_prism \<equiv> make_prism
    (\<lambda>cs. concat (List.map (prism_embed c_short_byte_prism) cs))
    decode_c_short_list\<close>

text \<open>
  Validity of @{const c_short_list_byte_prism}: Each @{type c_short} is encoded as exactly
  2 bytes via @{const c_short_byte_prism}. Decoding splits the byte list into 2-byte chunks
  and decodes each chunk.
\<close>

lemma c_short_byte_prism_embed_length:
  shows \<open>length (prism_embed c_short_byte_prism c) = 2\<close>
unfolding c_short_byte_prism_def prism_compose_def word_sword_iso_prism_def iso_prism_def
  word16_byte_list_prism_le_def list_fixlen_prism_def by (simp add: list_fixlen_embed_def)

lemma decode_encode_c_short_list:
  shows \<open>decode_c_short_list (concat (List.map (prism_embed c_short_byte_prism) cs)) = Some cs\<close>
proof (induction cs)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain a b where ab: \<open>prism_embed c_short_byte_prism c = [a, b]\<close>
    using c_short_byte_prism_embed_length[of c] by (metis (no_types, opaque_lifting) length_0_conv
      length_Cons length_tl list.sel(3) numeral_2_eq_2 Suc_length_conv)
  have proj: \<open>prism_project c_short_byte_prism [a, b] = Some c\<close>
    using is_valid_prism_def[of c_short_byte_prism] c_byte_prism_valid(4) ab by metis
  show ?case
    using Cons.IH by (simp add: ab proj)
qed

lemma encode_decode_c_short_list:
  shows \<open>decode_c_short_list bs = Some cs \<Longrightarrow>
    bs = concat (List.map (prism_embed c_short_byte_prism) cs)\<close>
proof (induction bs arbitrary: cs rule: decode_c_short_list.induct)
  case 1
  then show ?case by simp
next
  case (2 v)
  then show ?case by simp
next
  case (3 a b rest)
  from 3(2) obtain c where proj: \<open>prism_project c_short_byte_prism [a, b] = Some c\<close> and
      mc: \<open>map_option ((#) c) (decode_c_short_list rest) = Some cs\<close>
    by (cases \<open>prism_project c_short_byte_prism [a, b]\<close>) auto
  from mc obtain cs' where rest_decode: \<open>decode_c_short_list rest = Some cs'\<close> and
        cs_eq: \<open>cs = c # cs'\<close>
    by (cases \<open>decode_c_short_list rest\<close>) auto
  have embed: \<open>[a, b] = prism_embed c_short_byte_prism c\<close>
    using is_valid_prism_def[of c_short_byte_prism] c_byte_prism_valid(4) proj by metis
  have \<open>rest = concat (List.map (prism_embed c_short_byte_prism) cs')\<close>
    using 3(1)[OF proj rest_decode] .
  then show ?case
    by (simp add: cs_eq embed)
qed

lemma c_short_list_byte_prism_valid:
  shows \<open>is_valid_prism c_short_list_byte_prism\<close>
unfolding is_valid_prism_def c_short_list_byte_prism_def by (auto simp: decode_encode_c_short_list
  dest: encode_decode_c_short_list)

subsection \<open>Struct iso prisms\<close>

definition c_mlk_poly_struct_prism :: \<open>(c_short list, c_mlk_poly) prism\<close> where
  \<open>c_mlk_poly_struct_prism \<equiv> iso_prism make_c_mlk_poly c_mlk_poly_coeffs\<close>

definition c_mlk_poly_mulcache_struct_prism :: \<open>(c_short list, c_mlk_poly_mulcache) prism\<close> where
  \<open>c_mlk_poly_mulcache_struct_prism \<equiv> iso_prism make_c_mlk_poly_mulcache c_mlk_poly_mulcache_coeffs\<close>

lemma c_mlk_poly_struct_prism_valid:
  shows \<open>is_valid_prism c_mlk_poly_struct_prism\<close>
unfolding c_mlk_poly_struct_prism_def by (rule iso_prism_valid) auto

lemma c_mlk_poly_mulcache_struct_prism_valid:
  shows \<open>is_valid_prism c_mlk_poly_mulcache_struct_prism\<close>
unfolding c_mlk_poly_mulcache_struct_prism_def by (rule iso_prism_valid) auto

subsection \<open>Composed byte prisms for struct types\<close>

definition c_mlk_poly_byte_prism :: \<open>(8 word list, c_mlk_poly) prism\<close> where
  \<open>c_mlk_poly_byte_prism \<equiv> prism_compose c_short_list_byte_prism c_mlk_poly_struct_prism\<close>

definition c_mlk_poly_mulcache_byte_prism :: \<open>(8 word list, c_mlk_poly_mulcache) prism\<close> where
  \<open>c_mlk_poly_mulcache_byte_prism \<equiv>
    prism_compose c_short_list_byte_prism c_mlk_poly_mulcache_struct_prism\<close>

lemma c_mlk_poly_byte_prism_valid:
  shows \<open>is_valid_prism c_mlk_poly_byte_prism\<close>
unfolding c_mlk_poly_byte_prism_def by (intro prism_compose_valid c_short_list_byte_prism_valid
  c_mlk_poly_struct_prism_valid)

lemma c_mlk_poly_mulcache_byte_prism_valid:
  shows \<open>is_valid_prism c_mlk_poly_mulcache_byte_prism\<close>
unfolding c_mlk_poly_mulcache_byte_prism_def by (intro prism_compose_valid
  c_short_list_byte_prism_valid c_mlk_poly_mulcache_struct_prism_valid)

subsection \<open>Global interpretation of @{locale c_mlk_machine_model}\<close>

text \<open>
  The parameter order follows Isabelle's locale convention: implicit parameters
  from parent locales (here: @{locale reference}) come first, then the explicit
  parameters from the \<open>for\<close> clause.
  We provide trivial dummy implementations for @{locale c_pointer_model} parameters.
\<close>

global_interpretation mlk_instance: c_mlk_machine_model
  \<comment> \<open>Implicit @{locale reference} parameters\<close>
  urust_heap_update_raw_fun
  urust_heap_dereference_raw_fun
  urust_heap_reference_raw_fun
  urust_heap_points_to_raw'
  \<open>\<lambda>_. UNIV\<close> UNIV
  urust_heap_can_alloc_reference
  \<comment> \<open>@{locale c_pointer_model} for-clause parameters (dummy implementations)\<close>
  \<open>\<lambda>p _ _. p\<close>
  \<open>\<lambda>p _ _. p\<close>
  \<open>\<lambda>_ _ _. (0::int)\<close>
  \<open>\<lambda>_ _. False\<close>
  \<open>\<lambda>_ _. True\<close>
  \<open>\<lambda>_ _. True\<close>
  \<open>\<lambda>_ _. True\<close>
  \<open>\<lambda>_. (0::int)\<close>
  \<open>\<lambda>_. undefined\<close>
  \<comment> \<open>@{locale reference} type-constraining parameter\<close>
  \<open>\<lambda>_ _ _ _ _ _. ()\<close>
  \<comment> \<open>Prism parameters for @{locale reference_allocatable} instances\<close>
  c_mlk_poly_byte_prism
  c_mlk_poly_mulcache_byte_prism
  c_uint_byte_prism
  c_int_byte_prism
  c_short_byte_prism
  c_ushort_byte_prism
  c_short_list_byte_prism
  rewrites \<open>reference_defs.dereference_fun urust_heap_dereference_raw_fun =
              urust_heap_dereference_fun\<close>
       and \<open>reference_defs.update_fun urust_heap_update_raw_fun urust_heap_dereference_raw_fun =
              urust_heap_update_fun\<close>
       and \<open>reference_defs.reference_fun urust_heap_reference_raw_fun =
              urust_heap_reference_fun\<close>
proof -
  show \<open>c_mlk_machine_model
    urust_heap_update_raw_fun urust_heap_dereference_raw_fun
    urust_heap_reference_raw_fun urust_heap_points_to_raw'
    (\<lambda>_. UNIV) UNIV urust_heap_can_alloc_reference
    (\<lambda>p _ _. p) (\<lambda>_ _ _. (0::int)) (\<lambda>_ _. False) (\<lambda>_ _. True) (\<lambda>_ _. True)
    c_mlk_poly_byte_prism c_mlk_poly_mulcache_byte_prism
    c_uint_byte_prism c_int_byte_prism c_short_byte_prism
    c_ushort_byte_prism c_short_list_byte_prism\<close>
  proof
    \<comment> \<open>Prism validity for each @{locale reference_allocatable} instance\<close>
    show \<open>is_valid_prism c_mlk_poly_byte_prism\<close>
      by (rule c_mlk_poly_byte_prism_valid)
    show \<open>is_valid_prism c_mlk_poly_mulcache_byte_prism\<close>
      by (rule c_mlk_poly_mulcache_byte_prism_valid)
    show \<open>is_valid_prism c_uint_byte_prism\<close>
      by (rule c_byte_prism_valid(5))
    show \<open>is_valid_prism c_int_byte_prism\<close>
      by (rule c_byte_prism_valid(6))
    show \<open>is_valid_prism c_short_byte_prism\<close>
      by (rule c_byte_prism_valid(4))
    show \<open>is_valid_prism c_ushort_byte_prism\<close>
      by (rule c_byte_prism_valid(3))
    show \<open>is_valid_prism c_short_list_byte_prism\<close>
      by (rule c_short_list_byte_prism_valid)
    \<comment> \<open>Allocatability: @{term \<open>prism_dom p \<subseteq> UNIV\<close>} is trivially true for each prism\<close>
    show \<open>References.can_create_gref_for_prism c_mlk_poly_byte_prism\<close>
      by (simp add: References.can_create_gref_for_prism_def)
    show \<open>References.can_create_gref_for_prism c_mlk_poly_mulcache_byte_prism\<close>
      by (simp add: References.can_create_gref_for_prism_def)
    show \<open>References.can_create_gref_for_prism c_uint_byte_prism\<close>
      by (simp add: References.can_create_gref_for_prism_def)
    show \<open>References.can_create_gref_for_prism c_int_byte_prism\<close>
      by (simp add: References.can_create_gref_for_prism_def)
    show \<open>References.can_create_gref_for_prism c_short_byte_prism\<close>
      by (simp add: References.can_create_gref_for_prism_def)
    show \<open>References.can_create_gref_for_prism c_ushort_byte_prism\<close>
      by (simp add: References.can_create_gref_for_prism_def)
    show \<open>References.can_create_gref_for_prism c_short_list_byte_prism\<close>
      by (simp add: References.can_create_gref_for_prism_def)
  \<comment> \<open>@{locale c_pointer_model} axioms: trivially satisfied by dummy implementations\<close>
  qed auto
qed (auto simp: urust_heap_dereference_fun_def urust_heap_update_fun_def
                urust_heap_reference_fun_def)

end

