#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly mode="$1" log="$2"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
cd "$rt"
case "$mode" in
 prepare)
  [[ "$(sha256sum crates/aspis-core/src/v7_merkle208.rs | cut -d' ' -f1)" == 071ade1236140fdae559bb7b607ac9b7ee299e74eccb16b3385e3b1bbf215fdf ]] || exit 2
  git apply --check --recount "$ex/merkle-input.patch"
  git apply --recount "$ex/merkle-input.patch"
  sha256sum crates/aspis-core/src/v7_merkle208.rs "$ex/merkle_input_tests.rs" | tee "$log";;
 slices|borrow|both)
  extra="--cfg v8_merkle_$mode"
  [[ "$mode" != both ]] || extra='--cfg v8_merkle_slices --cfg v8_merkle_borrow'
  # Compilation dominates; bounded parent/frontier tests run optimized.
  systemd-run --user --scope --unit="aspis-merkle-$mode-test-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v env CARGO_TARGET_DIR="$ex/performance-host/target" RUSTFLAGS="$extra -C overflow-checks=yes -A unexpected_cfgs" cargo test --offline --locked --release --jobs 2 -p aspis-core --lib v7_merkle208:: -- --test-threads=1 --nocapture 2>&1 | tee "$log";;
 *) exit 2;;
esac
