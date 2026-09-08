#!/usr/bin/env bash
# Authorised NUC only; isolated source/cache, local simulation, no RPC/deploy.
set -euo pipefail
[[ $# == 3 && "$2" == /* && ! -e "$2" && -d "$3" ]] || { echo "usage: $0 MODE NEW_OUTPUT EXISTING_FIXTURES" >&2; exit 2; }
readonly mode="$1" rescue_out="$2" fixture_dir="$3"
readonly rescue_exp="$(cd "$(dirname "$0")" && pwd)"
readonly rescue_path=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
readonly rescue_tools=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc
flags="--cfg v8_performance_sbf --cfg v8_performance_fast --cfg v8_structured --cfg v8_fine_profile -A dead_code -A unexpected_cfgs"
cargo_config=()
case "$mode" in
 structured) ;;
 k) flags+=" --cfg v8_batch_k" ;;
 m) flags+=" --cfg v8_batch_m" ;;
 kernels) flags+=" --cfg v8_batch_m --cfg v8_tower_batch --cfg v8_query_kernels" ;;
 quiet) flags+=" --cfg v8_batch_m --cfg v8_tower_batch --cfg v8_query_kernels --cfg v8_quiet_profile" ;;
 semantic) flags+=" --cfg v8_batch_m --cfg v8_tower_batch --cfg v8_query_kernels --cfg v8_semantic_control" ;;
 fused|horner|gamma|reuse|grouped|best|best-quiet|best-overflow-control|best-core-overflow-control)
   flags+=" --cfg v8_batch_m --cfg v8_tower_batch --cfg v8_query_kernels --cfg v8_fused_rows"
   if [[ "$mode" != fused ]]; then flags+=" --cfg v8_shared_weights --cfg v8_block_horner"; fi
   if [[ "$mode" != fused && "$mode" != horner ]]; then flags+=" --cfg v8_gamma_wrap"; fi
   if [[ "$mode" == reuse || "$mode" == grouped || "$mode" == best* ]]; then flags+=" --cfg v8_reuse_gamma"; fi
   if [[ "$mode" == grouped || "$mode" == best* ]]; then flags+=" --cfg v8_grouped_linear"; fi
   if [[ "$mode" == best* ]]; then flags+=" --cfg v8_query_shared"; fi
   if [[ "$mode" == best-quiet ]]; then flags+=" --cfg v8_quiet_profile"; fi
   # Diagnostic ONLY: quantify release-codegen mismatch. Not the selected
   # checked implementation; blanket wrap semantics need their own audit.
   if [[ "$mode" == best-overflow-control ]]; then flags+=" -C overflow-checks=off"; fi
   if [[ "$mode" == best-core-overflow-control ]]; then cargo_config+=(--config 'profile.release.package.aspis-core.overflow-checks=false'); fi
   ;;
 *) echo "unknown mode" >&2; exit 2 ;;
esac
mkdir "$rescue_out"
readonly rescue_unit="aspis-v8-rescue-$mode-$(date +%s)-$$"
scope(){
 local part="$1"; shift
 systemd-run --user --scope --unit="$rescue_unit-$part" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 \
 /usr/bin/time -v env NO_DNA=1 PATH="$rescue_path" "$@"
}
scope build env RUSTC="$rescue_tools" RUSTFLAGS="$flags" cargo-build-sbf --offline --skip-tools-install \
 --no-rustup-override --tools-version v1.54 --jobs 2 --features selected-v7-kernels \
 --manifest-path "$rescue_exp/performance-sbf/Cargo.toml" --sbf-out-dir "$rescue_out/sbf" -- --locked "${cargo_config[@]}" \
 2>&1 | tee "$rescue_out/build.log"
if rg -q 'overflows the maximum allowed frame|Stack offset.*exceeded|Error:' "$rescue_out/build.log"; then
 echo "invalid SBF stack/build diagnostic" >&2; exit 1
fi
scope driver-build cargo build --offline --locked --release --jobs 2 --manifest-path "$rescue_exp/performance-svm/Cargo.toml" \
 2>&1 | tee "$rescue_out/driver-build.log"
scope run env ASPIS_V8_EXTENDED_REJECTIONS=1 "$rescue_exp/performance-svm/target/release/aspis-v8-performance-svm" "$rescue_out/sbf/aspis_v8_performance_sbf.so" "$fixture_dir" \
 2>&1 | tee "$rescue_out/svm.log"
sha256sum "$rescue_out/sbf/aspis_v8_performance_sbf.so" "$fixture_dir"/proof-{1,2,3}.bin \
 "$rescue_exp"/{relation_callback,inactive_row_binding,structured_weights,query_arithmetic,performance_verifier,performance}.rs \
 "$rescue_exp"/performance-svm/src/main.rs \
 | tee "$rescue_out/hashes.txt"
