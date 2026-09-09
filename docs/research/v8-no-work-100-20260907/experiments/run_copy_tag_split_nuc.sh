#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1" log="$2"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
cd "$rt"
case "$mode" in
prepare)
 [[ "$(sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | cut -d' ' -f1)" == 4befdbd2ab0799a9ba4062b4c0ce385534ae44acd27f2d7e2b990f7610001939 ]] || exit 2
 python3 "$ex/generate_copy_scatter.py" --check
 git apply --check --recount "$ex/copy-tag-split.patch"
 git apply --recount "$ex/copy-tag-split.patch"
 sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | tee "$log";;
prepare-bounded)
 [[ "$(sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | cut -d' ' -f1)" == de1596b23db4cdf11310c5b39bc6b3cc9aeae6edbac12e17c874912fde56c8cb ]] || exit 2
 git apply --check --recount "$ex/copy-tag-bounded.patch"
 git apply --recount "$ex/copy-tag-bounded.patch"
 sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | tee "$log";;
test|test-bounded)
 # Compilation dominates; the named arithmetic source gate is optimized.
 readonly flags='--cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan --cfg v8_copy_tag_split --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial -C overflow-checks=yes -A unexpected_cfgs'
 readonly features='pool-v1-kernel,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-active-mask-basis-audit'
 extra='';[[ "$mode" != test-bounded ]] || extra='--cfg v8_copy_tag_bounded'
 systemd-run --user --scope --unit="aspis-copy-tag-split-$mode-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env CARGO_TARGET_DIR="$ex/performance-host/target" RUSTFLAGS="$flags $extra" cargo test --offline --locked --release --jobs 2 -p aspis-statement --features "$features" --lib pool_v1::pair_forest_copy_terminal::tests:: -- --test-threads=1 --nocapture 2>&1 | tee "$log";;
*) exit 2;;
esac
