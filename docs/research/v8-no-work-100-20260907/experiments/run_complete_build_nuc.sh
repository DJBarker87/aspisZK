#!/usr/bin/env bash
# Task-owned source COPY with complete-integration.patch already applied.
# No production activation, remote deployment or unbounded build.
set -euo pipefail
readonly complete_exp="$(cd "$(dirname "$0")" && pwd)"
readonly complete_root="$(cd "$complete_exp/../../../.." && pwd)"
[[ "$complete_root" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$complete_root/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || { echo 'usage: script host|partial-host|sbf|hybrid|lazy|partial|profile|driver|pool|registry|v7|selected-v7|selected-pool|selected-registry NEW_LOG' >&2; exit 2; }
readonly mode="$1" log="$2"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
readonly common='--cfg v8_complete --cfg v8_performance_fast --cfg v8_structured --cfg v8_fine_profile --cfg v8_batch_m --cfg v8_tower_batch --cfg v8_query_kernels --cfg v8_fused_rows --cfg v8_shared_weights --cfg v8_block_horner --cfg v8_gamma_wrap --cfg v8_reuse_gamma --cfg v8_grouped_linear --cfg v8_query_shared --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_sparse_groups --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook --cfg v8_quiet_profile -A dead_code -A unexpected_cfgs'
scope(){ systemd-run --user --scope --unit="aspis-v8-complete-$mode-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v "$@"; }
case "$mode" in
host|partial-host|gamma-fixed-host)
 extra=''
 [[ "$mode" != partial-host ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial'
 [[ "$mode" != gamma-fixed-host ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan --cfg v8_copy_tag_split --cfg v8_copy_tag_bounded --cfg v8_copy_tag_shared --cfg v8_copy_tag_offsets --cfg v8_gamma_fixed -C overflow-checks=yes'
 scope env RUSTFLAGS="$common --cfg v8_payment_extraction --cfg v8_performance $extra" cargo build --offline --locked --release --jobs 2 --features insecure-spend-fixture,selected-v7-kernels --manifest-path "$complete_exp/performance-host/Cargo.toml" 2>&1 | tee "$log";;
sbf|hybrid|lazy|profile|partial|channel|group|channel-profile|suffix|tag7|scatter|tag-split|tag-bounded|tag-shared|tag-offset|tag-offset-profile|gamma-fixed|merkle-slices|merkle-borrow|merkle-both|leaf-record|decode-profile|gamma-fused|decode-blocks|auth-order|chord-norm)
 lineage="$mode"
 case "$mode" in gamma-fused|decode-blocks|auth-order|chord-norm) lineage=leaf-record;; esac
 case "$mode" in scatter|tag-split|tag-bounded) python3 "$complete_exp/generate_copy_scatter.py" --check;; esac
 [[ "$mode" != tag-shared ]] || python3 "$complete_exp/generate_tag_shared.py" --check
 case "$lineage" in tag-offset|tag-offset-profile|gamma-fixed|merkle-slices|merkle-borrow|merkle-both|leaf-record|decode-profile) python3 "$complete_exp/generate_tag_offsets.py" --check;; esac
 extra=''
 [[ "$mode" != hybrid ]] || extra='--cfg v8_qm_hybrid'
 [[ "$mode" != lazy ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0'
 [[ "$mode" != partial ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial'
 [[ "$mode" != channel ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial'
 [[ "$mode" != group ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_qm_group_partial'
 [[ "$mode" != suffix ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix'
 [[ "$mode" != tag7 ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix --cfg v8_copy_tag7'
 [[ "$mode" != scatter ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan'
 [[ "$mode" != tag-split ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan --cfg v8_copy_tag_split'
 [[ "$mode" != tag-bounded ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan --cfg v8_copy_tag_split --cfg v8_copy_tag_bounded'
 [[ "$mode" != tag-shared ]] || extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan --cfg v8_copy_tag_split --cfg v8_copy_tag_bounded --cfg v8_copy_tag_shared'
 case "$lineage" in tag-offset|tag-offset-profile|gamma-fixed|merkle-slices|merkle-borrow|merkle-both|leaf-record|decode-profile) extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan --cfg v8_copy_tag_split --cfg v8_copy_tag_bounded --cfg v8_copy_tag_shared --cfg v8_copy_tag_offsets';; esac
 case "$lineage" in gamma-fixed|merkle-slices|merkle-borrow|merkle-both|leaf-record|decode-profile) extra="$extra --cfg v8_gamma_fixed";; esac
 [[ "$mode" != merkle-slices ]] || extra="$extra --cfg v8_merkle_slices"
 [[ "$mode" != merkle-borrow ]] || extra="$extra --cfg v8_merkle_borrow"
 [[ "$mode" != merkle-both ]] || extra="$extra --cfg v8_merkle_slices --cfg v8_merkle_borrow"
 case "$lineage" in leaf-record|decode-profile) extra="$extra --cfg v8_merkle_slices --cfg v8_merkle_borrow --cfg v8_leaf_record";; esac
 [[ "$mode" != gamma-fused ]] || extra="$extra --cfg v8_gamma_fused"
 case "$mode" in decode-blocks|auth-order|chord-norm) extra="$extra --cfg v8_decode_blocks";; esac
 case "$mode" in auth-order|chord-norm) extra="$extra --cfg v8_auth_order";; esac
 [[ "$mode" != chord-norm ]] || extra="$extra --cfg v8_chord_norm"
 selected="$common"
 if [[ "$mode" == decode-profile ]];then extra="$extra --cfg v8_terminal_profile --cfg v8_decode_profile";selected="${common/--cfg v8_quiet_profile/}";fi
 if [[ "$mode" == tag-offset-profile ]];then extra="$extra --cfg v8_terminal_profile";selected="${common/--cfg v8_quiet_profile/}";fi
 if [[ "$mode" == channel-profile ]];then extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_gamma_partial --cfg v8_qm_channel_partial --cfg v8_terminal_profile';selected="${common/--cfg v8_quiet_profile/}";fi
 if [[ "$mode" == profile ]];then extra='--cfg v8_qm_hybrid --cfg v8_qm_lazy_c0';selected="${common/--cfg v8_quiet_profile/}";fi
 scope env CARGO_TARGET_DIR="$complete_exp/performance-sbf/target" RUSTC=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc RUSTFLAGS="$selected --cfg v8_performance_sbf $extra" cargo-build-sbf --offline --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 --manifest-path "$complete_exp/complete-sbf/Cargo.toml" --sbf-out-dir "$complete_root/sbf-complete-$mode" 2>&1 | tee "$log";;
driver)
 scope env CARGO_TARGET_DIR="$complete_exp/performance-svm/target" RUSTFLAGS='--cfg v8_complete -A unexpected_cfgs' cargo build --offline --locked --release --jobs 2 --bin aspis-v7-pair-forest-combined-rejection --manifest-path "$complete_root/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml" 2>&1 | tee "$log";;
selected-v7|selected-pool|selected-registry)
 program="${mode#selected-}"; feature_args=()
 case "$program" in
  v7) program=verifier;feature_args=(--features v7-pair-forest-one-tx-candidate);;
  pool) feature_args=(--features v7-pair-forest-one-tx-candidate);;
 esac
 scope env CARGO_TARGET_DIR="$complete_exp/performance-sbf/target" RUSTC=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc RUSTFLAGS='-A dead_code -A unexpected_cfgs' cargo-build-sbf --offline --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 --no-default-features "${feature_args[@]}" --manifest-path "$complete_root/programs/aspis-$program/Cargo.toml" --sbf-out-dir "$complete_root/sbf-$mode" -- --locked 2>&1 | tee "$log";;
pool|registry|v7)
 manifest="$complete_exp/complete-$mode-sbf/Cargo.toml"
 [[ "$mode" != v7 ]] || manifest="$complete_exp/complete-sbf/Cargo.toml"
 scope env CARGO_TARGET_DIR="$complete_exp/performance-sbf/target" RUSTC=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc RUSTFLAGS='-A dead_code -A unexpected_cfgs' cargo-build-sbf --offline --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 --manifest-path "$manifest" --sbf-out-dir "$complete_root/sbf-matched-$mode" 2>&1 | tee "$log";;
*) exit 2;;
esac
