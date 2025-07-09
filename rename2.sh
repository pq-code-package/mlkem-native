#!/bin/bash

FUNCTIONS=$(perl -ne '
  if (/^#define\s+([a-zA-Z0-9_]+)/) {     # if line starts with #define and captures the name
    $name = $1;                            # save the name
    $line = $_;                            # save current line
    if (/\\\s*$/) {                       # if line ends with backslash
        $next = <>;                        # read next line
        $line .= $next;                    # append next line
    }
    if ($line =~ /^#define\s+[a-zA-Z0-9_]+\s*(?:\\\s*\n\s*)?MLK_NAMESPACE/) {
        print "$name\n";                   # print the name if MLK_NAMESPACE follows directly
    }
  }
' $(find . -name "*.[ch]") | sort -u)

# FUNCTIONS=$(grep -E -r "^#define[[:space:]]+[a-zA-Z0-9_]+[[:space:]]+MLK_NAMESPACE" --include "*.[ch]" . | \
#                 tr ':' ' ' | cut -d' ' -f3 | sort -u)

# Also add debug macros
# FUNCTIONS="$FUNCTIONS debug_assert debug_assert_bound debug_assert_abs_bound debug_assert_bound_2d debug_assert_abs_bound_2d"

FUNCTIONS="ntt_native intt_native poly_reduce_native poly_tomont_native poly_mulcache_compute_native polyvec_basemul_acc_montgomery_cached_k2_native polyvec_basemul_acc_montgomery_cached_k3_native polyvec_basemul_acc_montgomery_cached_k4_native poly_tobytes_native poly_frombytes_native poly_compress_d4_native poly_compress_d10_native poly_decompress_d4_native poly_decompress_d10_native poly_compress_d5_native poly_compress_d11_native poly_decompress_d5_native poly_decompress_d11_native"

FUNCTIONS="keccak_f1600_x1_native keccak_f1600_x2_native keccak_f1600_x4_native"

PERL_SCRIPT=$(mktemp)
cat > "$PERL_SCRIPT" << 'EOF'
use strict;
use warnings;

my $filename = $ARGV[0];
warn "Processing: $filename\n";

while (my $line = <>) {
    my $modified = $line;
EOF

# for f in $FUNCTIONS; do
#     echo "    \$modified =~ s/([^a-zA-Z0-9_])${f}([^a-zA-Z0-9_])/\$1mlk_${f}\$2/g;" >> "$PERL_SCRIPT"
#     echo "    \$modified =~ s/mlk_${f}\.([ch])/${f}.\$1/g;" >> "$PERL_SCRIPT"
# done
# echo "    \$modified =~ s/MLK_ASM_NAMESPACE\(mlk_/MLK_ASM_NAMESPACE(/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/MLK_ASM_FN_SYMBOL\(mlk_/MLK_ASM_FN_SYMBOL(/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/MLK_NAMESPACE\(mlk_/MLK_NAMESPACE(/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/MLK_NAMESPACE_K\(mlk_/MLK_NAMESPACE_K(/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/\(MLK_NAMESPACE\)mlk_/\(MLK_NAMESPACE\)/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/mlk_crypto/crypto/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/mlk_mlkem/mlk/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/mlk_mlk_/mlk_/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/nistkat-mlk_shake256/nistkat-shake256/g;" >> "$PERL_SCRIPT"

echo '    $modified =~ s!\[@!@\[!g;' >> "$PERL_SCRIPT"

# echo '    $modified =~ s/MLK_CONFIG_SECURITY_LEVEL/MLKEM_K/g;' >> "$PERL_SCRIPT"

# echo '    $modified =~ s/MLKEM_K/MLK_CONFIG_SECURITY_LEVEL/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_NAMESPACE_PREFIX/MLK_CONFIG_NAMESPACE_PREFIX/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_MULTILEVEL_BUILD_WITH_SHARED/MLK_CONFIG_MULTILEVEL_WITH_SHARED/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_MULTILEVEL_BUILD_NO_SHARED/MLK_CONFIG_MULTILEVEL_NO_SHARED/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_USE_NATIVE_BACKEND_ARITH/MLK_CONFIG_USE_NATIVE_BACKEND_ARITH/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_ARITH_BACKEND_FILE/MLK_CONFIG_ARITH_BACKEND_FILE/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_USE_NATIVE_BACKEND_FIPS202/MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_FIPS202_BACKEND_FILE/MLK_CONFIG_FIPS202_BACKEND_FILE/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_FIPS202_CUSTOM_HEADER/MLK_CONFIG_FIPS202_CUSTOM_HEADER/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_FIPS202X4_CUSTOM_HEADER/MLK_CONFIG_FIPS202X4_CUSTOM_HEADER/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_CUSTOM_ZEROIZE/MLK_CONFIG_CUSTOM_ZEROIZE/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_CUSTOM_RANDOMBYTES/MLK_CONFIG_CUSTOM_RANDOMBYTES/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_INTERNAL_API_QUALIFIER/MLK_CONFIG_INTERNAL_API_QUALIFIER/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_EXTERNAL_API_QUALIFIER/MLK_CONFIG_EXTERNAL_API_QUALIFIER/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_CT_TESTING_ENABLED/MLK_CONFIG_CT_TESTING_ENABLED/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_NO_ASM/MLK_CONFIG_NO_ASM/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_KEYGEN_PCT/MLK_CONFIG_KEYGEN_PCT/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/MLK_KEYGEN_PCT_BREAKAGE_TEST/MLK_CONFIG_KEYGEN_PCT_BREAKAGE_TEST/g;' >> "$PERL_SCRIPT"

# echo '    $modified =~ s/KECCAK_LANES/MLK_KECCAK_LANES/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/KECCAK_WAY/MLK_KECCAK_WAY/g;' >> "$PERL_SCRIPT"
# echo '    $modified =~ s/mlk_debug_assert/mlk_assert/g;' >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/KeccakF1600/keccakf1600/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/StateXORBytes/xor_bytes/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/StateExtractBytes/extract_bytes/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/StatePermute/permute/g;" >> "$PERL_SCRIPT"
# echo "    \$modified =~ s/mlk_KeccakP1600times4_PermuteAll_24rounds/mlk_keccakf1600x4_permute24/g;" >> "$PERL_SCRIPT"

cat >> "$PERL_SCRIPT" << 'EOF'
    print $modified;
}
EOF

# Process files in parallel using the script
# Use sysctl to get CPU count on macOS
NCPU=$(sysctl -n hw.ncpu)
# git ls-files -s | cut -f2 | grep "proofs/cbmc/" |grep -v tiny_sha3 | grep -v "^120000" | \
git ls-files -s | cut -f2 | grep -v tiny_sha3 | grep -v "^120000" | \
    xargs -P $NCPU -I {} sh -c "([ ! -L '{}' ] && perl -i'' -f '$PERL_SCRIPT' {}) || (echo 'Skip {}')"

rm "$PERL_SCRIPT"

FILES=$(git ls-files -s | grep -v "^120000" | cut -f2)
