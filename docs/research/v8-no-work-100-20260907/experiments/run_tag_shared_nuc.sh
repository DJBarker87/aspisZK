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
 [[ "$(sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | cut -d' ' -f1)" == 5bea021e1c6a9fb7af7143a089d31e8b4864c17dc68444ecd64ed7af9e977610 ]] || exit 2
 python3 "$ex/generate_tag_shared.py" --check
 git apply --check --recount "$ex/copy-tag-shared.patch"
 git apply --recount "$ex/copy-tag-shared.patch"
 sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs "$ex/copy_tag_shared_generated.rs" | tee "$log";;
test)
 # Compilation dominates. Arithmetic comparisons execute optimized and checked.
 readonly flags='--cfg v8_copy_suffix --cfg v8_copy_tag7 --cfg v8_copy_plan --cfg v8_copy_tag_split --cfg v8_copy_tag_bounded --cfg v8_copy_tag_shared --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial -C overflow-checks=yes -A unexpected_cfgs'
 readonly features='pool-v1-kernel,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-active-mask-basis-audit'
 systemd-run --user --scope --unit="aspis-tag-shared-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env CARGO_TARGET_DIR="$ex/performance-host/target" RUSTFLAGS="$flags" cargo test --offline --locked --release --jobs 2 -p aspis-statement --features "$features" --lib pool_v1::pair_forest_copy_terminal::tests:: -- --test-threads=1 --nocapture 2>&1 | tee "$log";;
*) exit 2;;
esac
