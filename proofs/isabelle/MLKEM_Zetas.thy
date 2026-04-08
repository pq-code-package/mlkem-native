(*<*)
theory MLKEM_Zetas
  imports MLKEM_Spec
begin
(*>*)

text \<open>
  Precomputed twiddle factors for the NTT: 128 centered Montgomery-form
  powers of the primitive 256th root of unity modulo @{const MLKEM_Q}.
  Connects the C global @{verbatim "mlk_zetas[128]"} to its mathematical
  derivation via @{const montgomery_reduce_int} and bit reversal, and
  provides the word-level table used by @{const fqmul_int}.
\<close>

section \<open>Zetas Table\<close>

text \<open>128 precomputed twiddle factors (signed), matching the C global
  @{verbatim "mlk_zetas[128]"} from @{file "../../mlkem/src/poly.c"}.\<close>

(*<*)
definition zetas_int :: \<open>int list\<close> where
  \<open>zetas_int \<equiv> [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577,
    182, 962, -1202, -1474, 1468, 573, -1325, 264, 383, -829, 1458,
    -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571, 1223,
    652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666,
    -1618, -1162, 126, 1469, -853, -90, -271, 830, 107, -1421, -247,
    -951, -398, 961, -1508, -725, 448, -1065, 677, -1275, -1103, 430,
    555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291,
    -460, 1574, 1653, -246, 778, 1159, -147, -777, 1483, -602, 1119,
    -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097, 603,
    610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220,
    -1187, -1659, -1185, -1530, -1278, 794, -1510, -854, -870, 478, -108,
    -308, 996, 991, 958, -1460, 1522, 1628]\<close>

lemma length_zetas_int [simp]:
  shows \<open>length zetas_int = 128\<close>
by eval
(*>*)

subsection \<open>Mathematical Characterization\<close>

text \<open>The zetas table is derived from a primitive 256th root of unity
  modulo @{const MLKEM_Q}. The root @{text "\<zeta> = 17"} satisfies
  @{text "\<zeta>^256 \<equiv> 1 (mod Q)"} and @{text "\<zeta>^128 \<equiv> -1 (mod Q)"},
  confirming that its multiplicative order is exactly 256.\<close>

definition mlkem_zeta :: int where
  \<open>mlkem_zeta \<equiv> 17\<close>

lemma mlkem_zeta_is_root_of_unity:
  shows \<open>mlkem_zeta ^ 256 mod MLKEM_Q = 1\<close>
by eval

lemma mlkem_zeta_half_order:
  shows \<open>mlkem_zeta ^ 128 mod MLKEM_Q = MLKEM_Q - 1\<close>
by eval

lemma mlkem_zeta_primitive:
  shows \<open>list_all (\<lambda>k. mlkem_zeta ^ k mod MLKEM_Q \<noteq> 1) [1..<256]\<close>
by eval

text \<open>Bit reversal on @{term n} bits: reverses the @{term n} least significant
  bits of a natural number. Maps linear indices to the bit-reversed order
  used by the NTT butterfly decomposition.\<close>

fun bit_reverse :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bit_reverse 0 _ = 0\<close>
| \<open>bit_reverse (Suc n) k = (k mod 2) * 2 ^ n + bit_reverse n (k div 2)\<close>

text \<open>Centered modular reduction: maps @{term x} to its unique representative
  in @{text "{-\<lfloor>q/2\<rfloor>, \<dots>, \<lfloor>q/2\<rfloor>}"}.\<close>

definition centered_mod :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>centered_mod x q \<equiv> let r = x mod q in if 2 * r > q then r - q else r\<close>

text \<open>Each entry of the zetas table is the centered Montgomery-form power of
  the primitive root @{const mlkem_zeta} in bit-reversed order:
  @{text "zetas_int ! i = centered_mod (\<zeta>^(bit_reverse 7 i) \<sqdot> 2^16) Q"}.
  The factor @{text "2^16"} is the Montgomery radix used by
  @{const montgomery_reduce_int}.\<close>

lemma zetas_int_roots_of_unity:
  shows \<open>zetas_int =
    List.map (\<lambda>i. centered_mod (mlkem_zeta ^ bit_reverse 7 i * 2 ^ 16) MLKEM_Q) [0..<128]\<close>
by eval

subsection \<open>Word-Level Zetas\<close>

text \<open>Word-level zetas table, derived from the canonical @{const zetas_int}.\<close>

definition zetas_sword :: \<open>16 sword list\<close> where
  \<open>zetas_sword \<equiv> List.map word_of_int zetas_int\<close>

(*<*)
lemma zetas_sword_unfold:
  shows \<open>zetas_sword = [0xFBEC, 0xFD0A, 0xFE99, 0xFA13, 0x5D5, 0x58E, 0x11F, 0xCA,
    0xFF55, 0x26E, 0x629, 0xB6, 0x3C2, 0xFB4E, 0xFA3E, 0x5BC,
    0x23D, 0xFAD3, 0x108, 0x17F, 0xFCC3, 0x5B2, 0xF9BE, 0xFF7E,
    0xFD57, 0x3F9, 0x2DC, 0x260, 0xF9FA, 0x19B, 0xFF33, 0xF9DD,
    0x4C7, 0x28C, 0xFDD8, 0x3F7, 0xFAF3, 0x5D3, 0xFEE6, 0xF9F8,
    0x204, 0xFFF8, 0xFEC0, 0xFD66, 0xF9AE, 0xFB76, 0x7E, 0x5BD,
    0xFCAB, 0xFFA6, 0xFEF1, 0x33E, 0x6B, 0xFA73, 0xFF09, 0xFC49,
    0xFE72, 0x3C1, 0xFA1C, 0xFD2B, 0x1C0, 0xFBD7, 0x2A5, 0xFB05,
    0xFBB1, 0x1AE, 0x22B, 0x34B, 0xFB1D, 0x367, 0x60E, 0x69,
    0x1A6, 0x24B, 0xB1, 0xFF15, 0xFEDD, 0xFE34, 0x626, 0x675,
    0xFF0A, 0x30A, 0x487, 0xFF6D, 0xFCF7, 0x5CB, 0xFDA6, 0x45F,
    0xF9CA, 0x284, 0xFC98, 0x15D, 0x1A2, 0x149, 0xFF64, 0xFFB5,
    0x331, 0x449, 0x25B, 0x262, 0x52A, 0xFAFB, 0xFA47, 0x180,
    0xFB41, 0xFF78, 0x4C2, 0xFAC9, 0xFC96, 0xDC, 0xFB5D, 0xF985,
    0xFB5F, 0xFA06, 0xFB02, 0x31A, 0xFA1A, 0xFCAA, 0xFC9A, 0x1DE,
    0xFF94, 0xFECC, 0x3E4, 0x3DF, 0x3BE, 0xFA4C, 0x5F2, 0x65C]\<close>
by eval
(*>*)

lemma length_zetas_sword [simp]:
  shows \<open>length zetas_sword = 128\<close>
by (simp add: zetas_sword_def)

(*<*)
lemma map_sint_zetas_sword:
  shows \<open>List.map sint zetas_sword = zetas_int\<close>
by eval
(*>*)

lemma zetas_sword_sint:
  assumes \<open>i < 128\<close>
    shows \<open>sint (zetas_sword ! i) = zetas_int ! i\<close>
using assms nth_map[of i zetas_sword sint] map_sint_zetas_sword by simp

(*<*)
lemma map_sint_neg_scast_zetas_sword:
  shows \<open>List.map (\<lambda>w :: 16 sword. sint (scast (- (scast w :: 32 sword)) :: 16 sword))
     zetas_sword = List.map uminus zetas_int\<close>
by eval
(*>*)

lemma zetas_neg_scast_sint:
  assumes \<open>i < 128\<close>
    shows \<open>sint (scast (- (scast (zetas_sword ! i) :: 32 sword)) :: 16 sword) =
             - (zetas_int ! i)\<close>
using assms nth_map[of i zetas_sword \<open>\<lambda>w. sint (scast (- (scast w :: 32 sword)) :: 16 sword)\<close>]
  nth_map[of i zetas_int uminus] map_sint_neg_scast_zetas_sword by simp

(*<*)
lemma drop_64_zetas_sword:
  shows \<open>drop 64 zetas_sword =
    [0xFBB1, 0x1AE, 0x22B, 0x34B, 0xFB1D, 0x367, 0x60E, 0x69,
     0x1A6, 0x24B, 0xB1, 0xFF15, 0xFEDD, 0xFE34, 0x626, 0x675,
     0xFF0A, 0x30A, 0x487, 0xFF6D, 0xFCF7, 0x5CB, 0xFDA6, 0x45F,
     0xF9CA, 0x284, 0xFC98, 0x15D, 0x1A2, 0x149, 0xFF64, 0xFFB5,
     0x331, 0x449, 0x25B, 0x262, 0x52A, 0xFAFB, 0xFA47, 0x180,
     0xFB41, 0xFF78, 0x4C2, 0xFAC9, 0xFC96, 0xDC, 0xFB5D, 0xF985,
     0xFB5F, 0xFA06, 0xFB02, 0x31A, 0xFA1A, 0xFCAA, 0xFC9A, 0x1DE,
     0xFF94, 0xFECC, 0x3E4, 0x3DF, 0x3BE, 0xFA4C, 0x5F2, 0x65C]\<close>
by eval
(*>*)

subsection \<open>Zetas Bounds\<close>

text \<open>Bounds on the abstract zetas coefficients.\<close>

lemma zetas_int_abs_bound:
  assumes \<open>i < 128\<close>
    shows \<open>\<bar>zetas_int ! i\<bar> \<le> 1659\<close>
proof -
  have \<open>list_all (\<lambda>z. \<bar>z\<bar> \<le> 1659) zetas_int\<close>
    by eval
  thus ?thesis
    using assms by (simp add: list_all_length)
qed

lemma zetas_int_bound:
  assumes \<open>i < 128\<close>
    shows \<open>zetas_int ! i \<le> 1659\<close> \<open>- (zetas_int ! i) \<le> 1659\<close>
using zetas_int_abs_bound[OF assms] by auto

lemma zetas_int_i32_bound_from_k:
  assumes \<open>k < 64\<close>
    shows \<open>zetas_int ! (127 - k) \<le> 2147483648\<close>
      and \<open>- (zetas_int ! (127 - k)) < 2147483648\<close>
proof -
  have \<open>127 - k < 128\<close>
    by simp
  from zetas_int_bound[OF this] show \<open>zetas_int ! (127 - k) \<le> 2147483648\<close>
    by simp
  from zetas_int_bound[OF \<open>127 - k < 128\<close>] show \<open>- (zetas_int ! (127 - k)) < 2147483648\<close>
    by simp
qed

subsection \<open>C Global Zetas\<close>

text \<open>Connecting the C global zetas array to the abstract spec.\<close>

lemma c_global_mlk_zetas_eq_zetas_sword:
  shows \<open>c_global_mlk_zetas = zetas_sword\<close>
by (simp add: c_global_mlk_zetas_def zetas_sword_unfold)

section \<open>Mulcache Computation\<close>

text \<open>Abstract mulcache: for each block of 4 coefficients, compute two
  fqmul products with the corresponding zeta factor.\<close>

definition mulcache_compute_int :: \<open>int_poly \<Rightarrow> int list\<close> where
  \<open>mulcache_compute_int ap \<equiv>
     concat (List.map (\<lambda>i. [fqmul_int (ap ! (4*i + 1)) (zetas_int ! (64 + i)),
                             fqmul_int (ap ! (4*i + 3)) (- (zetas_int ! (64 + i)))])
                      [0..<64])\<close>

lemma length_concat_map_pair:
  shows \<open>length (concat (List.map (\<lambda>j. [f j, g j]) [0..<n])) = 2 * n\<close>
by (induct n) simp_all

lemma length_mulcache_compute_int [simp]:
  shows \<open>length (mulcache_compute_int ap) = 128\<close>
unfolding mulcache_compute_int_def by (simp add: length_concat_map_pair)

lemma concat_map_pair_nth_aux:
  assumes \<open>i < n\<close>
    shows \<open>concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i) = f i
            \<and> concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i + 1) = g i\<close>
using assms proof (induct n arbitrary: i)
  case (Suc n)
  then show ?case
    by (cases \<open>i < n\<close>) (auto simp: nth_append less_Suc_eq length_concat_map_pair)
qed auto

lemma concat_map_pair_nth:
  assumes \<open>i < n\<close>
    shows \<open>concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i) = f i\<close>
      and \<open>concat (List.map (\<lambda>j. [f j, g j]) [0..<n]) ! (2*i + 1) = g i\<close>
using concat_map_pair_nth_aux[OF assms] by auto

lemma mulcache_compute_int_nth_even:
  assumes \<open>i < 64\<close>
    shows \<open>mulcache_compute_int ap ! (2*i) =
             fqmul_int (ap ! (4*i + 1)) (zetas_int ! (64 + i))\<close>
unfolding mulcache_compute_int_def using assms by (rule concat_map_pair_nth)

lemma mulcache_compute_int_nth_odd:
  assumes \<open>i < 64\<close>
    shows \<open>mulcache_compute_int ap ! (2*i + 1) =
             fqmul_int (ap ! (4*i + 3)) (- (zetas_int ! (64 + i)))\<close>
unfolding mulcache_compute_int_def using assms by (rule concat_map_pair_nth)

(*<*)
subsection \<open>Word Arithmetic Helpers\<close>

lemma word_of_nat_mult_numeral:
  shows \<open>(numeral n :: 'a::len word) * word_of_nat k = word_of_nat (numeral n * k)\<close>
by (metis of_nat_mult of_nat_numeral)

lemma unat_word_sub_word_of_nat:
    fixes c :: \<open>32 word\<close>
  assumes \<open>unat c = n\<close> \<open>m \<le> n\<close>
    shows \<open>unat (c - word_of_nat m) = n - m\<close>
proof -
  have \<open>n < 2 ^ 32\<close>
    using assms(1) unat_lt2p[of c] by simp
  hence \<open>m < 2 ^ 32\<close>
    using assms(2) by linarith
  hence u: \<open>unat (word_of_nat m :: 32 word) = m\<close>
    by (simp add: unat_of_nat)
  have le: \<open>(word_of_nat m :: 32 word) \<le> c\<close>
    using assms by (simp add: word_le_nat_alt u)
  show ?thesis
    using unat_sub[OF le] u assms by simp
qed

lemma unat_0xFD_sub_4k [simp]:
  assumes \<open>k < 64\<close>
    shows \<open>unat ((0xFD :: 32 word) - 4 * word_of_nat k) = 253 - 4 * k\<close>
using assms by (simp del: of_nat_mult of_nat_numeral
  add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0xFF_sub_4k [simp]:
  assumes \<open>k < 64\<close>
    shows \<open>unat ((0xFF :: 32 word) - 4 * word_of_nat k) = 255 - 4 * k\<close>
using assms by (simp del: of_nat_mult of_nat_numeral
  add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0x7E_sub_2k [simp]:
  assumes \<open>k < 64\<close>
    shows \<open>unat ((0x7E :: 32 word) - 2 * word_of_nat k) = 126 - 2 * k\<close>
using assms by (simp del: of_nat_mult of_nat_numeral
 add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0x7F_sub_2k [simp]:
  assumes \<open>k < 64\<close>
    shows \<open>unat ((0x7F :: 32 word) - 2 * word_of_nat k) = 127 - 2 * k\<close>
using assms by (simp del: of_nat_mult of_nat_numeral
  add: word_of_nat_mult_numeral unat_of_nat unat_sub word_le_nat_alt)

lemma unat_0x7F_sub_k [simp]:
  assumes \<open>k < 128\<close>
    shows \<open>unat ((0x7F :: 32 word) - word_of_nat k) = 127 - k\<close>
using assms by (intro unat_word_sub_word_of_nat) simp_all

subsection \<open>Downward-Counting Indexing\<close>

lemma mulcache_compute_int_nth_even':
  assumes \<open>k < 64\<close>
    shows \<open>mulcache_compute_int ap ! (126 - 2 * k) =
             fqmul_int (ap ! (253 - 4 * k)) (zetas_int ! (127 - k))\<close>
proof -
  define i where
    \<open>i = 63 - k\<close>
  with assms have \<open>i < 64\<close>
    by simp
  have idx: \<open>126 - 2 * k = 2 * i\<close> \<open>253 - 4 * k = 4 * i + 1\<close> \<open>127 - k = 64 + i\<close>
    unfolding i_def using assms by auto
  show ?thesis unfolding idx
    by (rule mulcache_compute_int_nth_even[OF \<open>i < 64\<close>])
qed

lemma mulcache_compute_int_nth_odd':
  assumes \<open>k < 64\<close>
    shows \<open>mulcache_compute_int ap ! (127 - 2 * k) =
             fqmul_int (ap ! (255 - 4 * k)) (- (zetas_int ! (127 - k)))\<close>
proof -
  define i where
    \<open>i = 63 - k\<close>
  with assms have \<open>i < 64\<close>
    by simp
  have idx: \<open>127 - 2 * k = 2 * i + 1\<close> \<open>255 - 4 * k = 4 * i + 3\<close> \<open>127 - k = 64 + i\<close>
    unfolding i_def using assms by auto
  show ?thesis unfolding idx
    by (rule mulcache_compute_int_nth_odd[OF \<open>i < 64\<close>])
qed
(*>*)

(*<*)
end
(*>*)
