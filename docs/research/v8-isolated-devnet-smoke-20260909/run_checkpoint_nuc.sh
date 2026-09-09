#!/usr/bin/env bash
# Bounded, cached compilation and the exact eight-lane snapshot regression.
set -euo pipefail
readonly demo="$(cd "$(dirname "$0")" && pwd)"
readonly root="$(cd "$demo/../../.." && pwd)"
[[ "$root" == /home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909 && ! -e "$root/.git" ]]
[[ $# == 2 && ! -e "$2" ]] || { echo 'usage: build-pool|build-diagnostic|diagnostic NEW_LOG'; exit 2; }
readonly mode="$1" log="$2" ex="$root/docs/research/v8-no-work-100-20260907/experiments"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
cd "$root"
# Compilation is the heavy step; diagnostic execution is optimized and bounded.
# Inspect host reservations before invoking; each invocation reserves 7 GiB.
scope(){ systemd-run --user --scope --unit="aspis-checkpoint-$mode-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v "$@"; }
case "$mode" in
build-pool)
 scope env CARGO_TARGET_DIR="$ex/performance-sbf/target" RUSTC=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc RUSTFLAGS='-A dead_code -A unexpected_cfgs --cfg v8_pool_zero --cfg v8_checkpoint_receipts' cargo-build-sbf --offline --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 --no-default-features --features v7-pair-forest-one-tx-candidate --manifest-path programs/aspis-pool/Cargo.toml --sbf-out-dir sbf-checkpoint-receipts-v2 -- --locked 2>&1 | tee "$log";;
build-diagnostic)
 cp "$demo/checkpoint_receipt_diagnostic.rs" results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/bin/checkpoint_receipt_diagnostic.rs
 scope env CARGO_TARGET_DIR="$root/checkpoint-svm-target" cargo build --offline --release --locked --jobs 2 --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml --bin checkpoint_receipt_diagnostic 2>&1 | tee "$log";;
diagnostic)
 scope checkpoint-svm-target/release/checkpoint_receipt_diagnostic "$demo/evidence/live/all-lanes-checkpoint-blocked-state.json" "$demo/first-setup-plan.json" sbf-checkpoint-receipts-v2/aspis_pool.so 2>&1 | tee "$log";;
*) exit 2;;
esac
