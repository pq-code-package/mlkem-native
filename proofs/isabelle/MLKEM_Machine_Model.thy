theory MLKEM_Machine_Model
  imports "Micro_C_Examples.Simple_C_Functions"
begin

(*<*)
text \<open>
  Machine-model assumptions used by generated \<^verbatim>\<open>mlkem-native\<close> C definitions.
  Types are extracted first so locale assumptions can depend on the generated
  C record/datatype names.
\<close>

micro_c_file manifest: "generated/manifests/poly.types.manifest" "generated/c/poly.pre.c"

locale c_mlk_machine_model =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff
        c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
        c_ptr_to_uintptr c_uintptr_to_ptr +
    reference reference_types +
    ref_c_mlk_poly: reference_allocatable reference_types _ _ _ _ _ _ _ c_mlk_poly_prism +
    ref_c_mlk_poly_mulcache: reference_allocatable reference_types _ _ _ _ _ _ _ c_mlk_poly_mulcache_prism +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism +
    ref_c_short: reference_allocatable reference_types _ _ _ _ _ _ _ c_short_prism +
    ref_c_ushort: reference_allocatable reference_types _ _ _ _ _ _ _ c_ushort_prism +
    ref_c_short_list: reference_allocatable reference_types _ _ _ _ _ _ _ c_short_list_prism
  for c_ptr_add :: \<open>('addr, 8 word list) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('addr, 8 word list) gref\<close>
  and c_ptr_shift_signed :: \<open>('addr, 8 word list) gref \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ('addr, 8 word list) gref\<close>
  and c_ptr_diff :: \<open>('addr, 8 word list) gref \<Rightarrow> ('addr, 8 word list) gref \<Rightarrow> nat \<Rightarrow> int\<close>
  and c_ptr_less :: \<open>('addr, 8 word list) gref \<Rightarrow> ('addr, 8 word list) gref \<Rightarrow> bool\<close>
  and c_ptr_le :: \<open>('addr, 8 word list) gref \<Rightarrow> ('addr, 8 word list) gref \<Rightarrow> bool\<close>
  and c_ptr_greater :: \<open>('addr, 8 word list) gref \<Rightarrow> ('addr, 8 word list) gref \<Rightarrow> bool\<close>
  and c_ptr_ge :: \<open>('addr, 8 word list) gref \<Rightarrow> ('addr, 8 word list) gref \<Rightarrow> bool\<close>
  and c_ptr_to_uintptr :: \<open>('addr, 8 word list) gref \<Rightarrow> int\<close>
  and c_uintptr_to_ptr :: \<open>int \<Rightarrow> ('addr, 8 word list) gref\<close>
  and reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 8 word list \<Rightarrow> c_abort \<Rightarrow> 'i prompt \<Rightarrow>
        'o prompt_output \<Rightarrow> unit\<close>
  and c_mlk_poly_prism :: \<open>(8 word list, c_mlk_poly) prism\<close>
  and c_mlk_poly_mulcache_prism :: \<open>(8 word list, c_mlk_poly_mulcache) prism\<close>
  and c_uint_prism :: \<open>(8 word list, c_uint) prism\<close>
  and c_int_prism :: \<open>(8 word list, c_int) prism\<close>
  and c_short_prism :: \<open>(8 word list, c_short) prism\<close>
  and c_ushort_prism :: \<open>(8 word list, c_ushort) prism\<close>
  and c_short_list_prism :: \<open>(8 word list, c_short list) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_mlk_poly.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_mlk_poly_mulcache.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_short.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_ushort.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_short_list.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end
(*>*)

end
