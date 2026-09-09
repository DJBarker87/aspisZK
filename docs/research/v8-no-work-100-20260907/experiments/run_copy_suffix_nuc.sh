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
 [[ "$(sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | cut -d' ' -f1)" == 50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5 ]] || exit 2
 git apply --check --recount "$ex/copy-suffix.patch"
 git apply --recount "$ex/copy-suffix.patch"
 sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | tee "$log";;
prepare-tag7)
 [[ "$(sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | cut -d' ' -f1)" == 59884f82f3fd365b6d2fb0a7cdc5b73743377a9dc46ddb9660609c7f3aed7ad9 ]] || exit 2
 git apply --check --recount "$ex/copy-tag7.patch"
 git apply --recount "$ex/copy-tag7.patch"
 sha256sum crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | tee "$log";;
test|test-tag7)
 # Time is expected in compilation, followed by small, optimized actual-source
 # arbitrary-opening differentials; no proof generation or elimination here.
 readonly flags='--cfg v8_copy_suffix --cfg v8_range_m31 --cfg v8_range_cm31 --cfg v8_range_dots --cfg v8_cm_schoolbook --cfg v8_prepared_schoolbook --cfg v8_qm_hybrid --cfg v8_qm_lazy_c0 --cfg v8_qm_channel_partial -C overflow-checks=yes -A unexpected_cfgs'
 readonly features='pool-v1-kernel,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-active-mask-basis-audit'
 extra=''; [[ "$mode" != test-tag7 ]] || extra='--cfg v8_copy_tag7'
 systemd-run --user --scope --unit="aspis-copy-suffix-$mode-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env CARGO_TARGET_DIR="$ex/performance-host/target" RUSTFLAGS="$flags $extra" cargo test --offline --locked --release --jobs 2 -p aspis-statement --features "$features" --lib pool_v1::pair_forest_copy_terminal::tests:: -- --test-threads=1 --nocapture 2>&1 | tee "$log";;
*) exit 2;;
esac
