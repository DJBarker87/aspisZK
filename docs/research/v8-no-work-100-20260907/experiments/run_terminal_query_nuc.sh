#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$1"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
cd "$rt"
mode=terminal-prefix;fixed=''
if [[ "${ASPIS_TERMINAL_FIXED:-0}" == 1 ]];then mode=terminal-fixed;fixed='--cfg v8_terminal_fixed';fi
if [[ "${ASPIS_TERMINAL_FUSED:-0}" == 1 ]];then mode=terminal-fused;fixed='--cfg v8_terminal_fixed --cfg v8_terminal_fused';fi
if [[ "${ASPIS_TERMINAL_STACK:-0}" == 1 ]];then mode=terminal-stack;fixed='--cfg v8_terminal_fixed --cfg v8_terminal_fused --cfg v8_semantic_stack';fi
bash "$ex/check_terminal_query_sources.sh" "$mode" test
readonly extra="--cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial $fixed"
# Compilation dominates; bounded changed-kernel differential tests only.
systemd-run --user --scope --unit="aspis-terminal-query-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env RUSTFLAGS="--cfg v8_payment_extraction --cfg v8_performance --cfg v8_performance_fast --cfg v8_terminal_prefix --cfg v8_structured --cfg v8_shared_weights --cfg v8_reuse_gamma --cfg v8_shared_gamma --cfg v8_semantic_boundary --cfg v8_semantic_carry --cfg v8_affine_primal --cfg v8_query_kernels --cfg v8_quotient_fused --cfg v8_query_shared --cfg v8_line_norm --cfg v8_split_inverse --cfg v8_joined_inverse --cfg v8_circle_norm --cfg v8_chord_norm --cfg v8_batch_m --cfg v8_leaf_record --cfg v8_merkle_slices --cfg v8_merkle_borrow -C overflow-checks=yes -A dead_code -A unexpected_cfgs $extra" cargo test --offline --locked --release --jobs 2 --features insecure-spend-fixture,selected-v7-kernels --manifest-path "$ex/performance-host/Cargo.toml" terminal_query::tests -- --test-threads=1 --nocapture 2>&1 | tee "$log"
rg -q "test result: ok. 1 passed; 0 failed" "$log"
rg -q "TERMINAL_QUERY arbitrary_batches=1024" "$log"
sha256sum "$ex/relation_callback.rs" "$ex/circle_norm.rs" "$ex/joined_inverse.rs" "$ex/line_norm.rs" "$ex/quotient_fold.rs" "$ex/affine_primal.rs" "$ex/semantic_carry.rs" "$ex/semantic_boundary.rs" "$ex/performance_verifier.rs" "$ex/shared_gamma.rs" "$ex/structured_weights.rs" "$ex/terminal_query.rs" "$rt/crates/aspis-core/src/sumcheck.rs" "$rt/crates/aspis-core/src/field.rs" >> "$log"
