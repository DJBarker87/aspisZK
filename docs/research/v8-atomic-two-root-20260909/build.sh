#!/usr/bin/env bash
set -euo pipefail
ex="$(cd "$(dirname "$0")" && pwd)"
rt="$(cd "$ex/../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-atomic-two-root-20260909 && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || exit 2
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
cache="$rt/docs/research/v8-no-work-100-20260907/experiments"
scope(){ systemd-run --user --scope --unit="aspis-atomic-$1-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v "${@:2}"; }
case "$1" in
 inbox)
  # Expensive phase: optimized compilation; no proof generation/elimination.
  scope inbox env CARGO_TARGET_DIR="$cache/performance-sbf/target" RUSTC=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc \
    RUSTFLAGS='-A unexpected_cfgs -A deprecated' cargo-build-sbf --offline --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 \
    --manifest-path "$ex/inbox/Cargo.toml" --sbf-out-dir "$rt/artifacts/inbox" -- --locked 2>&1 | tee "$2"
  ! rg -q 'Stack offset.*exceeded|overflows the maximum allowed frame|Error:|error:' "$2";;
 prover)
  scope prover env RUSTFLAGS="--cfg v8_complete --cfg v8_payment_extraction --cfg v8_performance --cfg v8_performance_fast --cfg v8_structured -A dead_code -A unexpected_cfgs -C overflow-checks=yes" \
    cargo build --release --offline --locked --jobs 2 --features insecure-spend-fixture,selected-v7-kernels --manifest-path "$cache/performance-host/Cargo.toml" 2>&1 | tee "$2";;
 driver)
  scope driver env CARGO_TARGET_DIR="$cache/performance-svm/target" RUSTFLAGS='--cfg v8_complete -A unexpected_cfgs' \
    cargo build --release --offline --locked --jobs 2 --manifest-path "$rt/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml" 2>&1 | tee "$2";;
 *) exit 2;;
esac
