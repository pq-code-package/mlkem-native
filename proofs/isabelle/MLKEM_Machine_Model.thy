theory MLKEM_Machine_Model
  imports "Micro_C_Examples.Simple_C_Functions"
begin

text \<open>
  Machine-model assumptions used by generated \<^verbatim>\<open>mlkem-native\<close> C definitions.
  Types are extracted first so locale assumptions can depend on the generated
  C record/datatype names.
\<close>

micro_c_file manifest: "generated/manifests/poly.types.manifest" "generated/c/poly.pre.c"

locale c_mlk_machine_model =
    reference reference_types +
    ref_c_mlk_poly: reference_allocatable reference_types _ _ _ _ _ _ _ c_mlk_poly_prism +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism +
    ref_c_short: reference_allocatable reference_types _ _ _ _ _ _ _ c_short_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow> 'i prompt \<Rightarrow>
        'o prompt_output \<Rightarrow> unit\<close>
  and c_mlk_poly_prism :: \<open>('gv, c_mlk_poly) prism\<close>
  and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
  and c_short_prism :: \<open>('gv, c_short) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_mlk_poly.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_short.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

end

end
