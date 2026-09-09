#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$1"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
cd "$rt"
bash "$ex/check_quotient_fold_sources.sh"
extra=''
if [[ "${ASPIS_QUOTIENT_SELECTED_KERNELS:-0}" == 1 ]];then
 extra='--cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial'
fi
# Compilation dominates; bounded changed-kernel differential tests only.
systemd-run --user --scope --unit="aspis-quotient-fold-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env RUSTFLAGS="--cfg v8_quotient_fused --cfg v8_query_shared --cfg v8_line_norm --cfg v8_split_inverse --cfg v8_joined_inverse --cfg v8_circle_norm --cfg v8_chord_norm --cfg v8_batch_m --cfg v8_leaf_record --cfg v8_merkle_slices --cfg v8_merkle_borrow -C overflow-checks=yes -A dead_code -A unexpected_cfgs $extra" cargo test --offline --locked --release --jobs 2 --manifest-path "$ex/performance-host/Cargo.toml" quotient_fold::tests -- --test-threads=1 --nocapture 2>&1 | tee "$log"
sha256sum "$ex/relation_callback.rs" "$ex/circle_norm.rs" "$ex/joined_inverse.rs" "$ex/line_norm.rs" "$ex/quotient_fold.rs" >> "$log"
