#!/usr/bin/env bash
# Existing task-owned COPY only; original Pool release policy and cached tools.
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" rt="$(cd "$(dirname "$0")/../../../.." && pwd)"
[[ "$rt" == /home/dombarker/project-offloads/aspis-v8-* && ! -e "$rt/.git" ]] || exit 2
[[ $# == 2 && ! -e "$2" ]] || { echo 'usage: script prepare|prepare-driver|test|profile-old|profile-fast|fast NEW_LOG';exit 2; }
readonly mode="$1" log="$2"
export NO_DNA=1 PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
cd "$rt"
scope(){ systemd-run --user --scope --unit="aspis-v8-zero-$mode-$(date +%s)-$$" -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 /usr/bin/time -v "$@"; }
case "$mode" in
prepare-token)
 [[ "$(sha256sum results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs | cut -d' ' -f1)" == d9f1532d94d1c9b9b5f5cc2171f88ca71c5a3e2e8d3dfb9691a098b56bc2976b ]] || exit 2
 git apply --check --recount "$ex/token-control-driver.patch"
 git apply --recount "$ex/token-control-driver.patch"
 sha256sum results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs | tee "$log";;
prepare-driver)
 [[ "$(sha256sum results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs | cut -d' ' -f1)" == 251aba0b81db74a2c6916c1a522d8a4e3fa63c422fa4797ada53d4132c0398f1 ]] || { echo 'Unexpected harness source; inspect without reset.';exit 2; }
 git apply --check --recount "$ex/pool-zero-driver.patch"
 git apply --recount "$ex/pool-zero-driver.patch"
 sha256sum results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs | tee "$log";;
prepare)
 [[ "$(sha256sum programs/aspis-pool/src/pair_forest.rs | cut -d' ' -f1)" == d96b352bae081a72d6e887759a356674598e0bf3a177c8d103885f02bc344c30 ]] || { echo 'Unexpected Pool source; inspect without reset.';exit 2; }
 git apply --check --unidiff-zero "$ex/pool-zero-page.patch"
 git apply --unidiff-zero "$ex/pool-zero-page.patch"
 sha256sum programs/aspis-pool/src/pair_forest.rs "$ex/zero_page.rs" | tee "$log";;
test)
 scope rustc --edition 2021 -O --test "$ex/zero_page.rs" -o "$rt/zero-page-test" 2>&1 | tee "$log"
 scope "$rt/zero-page-test" 2>&1 | tee -a "$log";;
profile-old|profile-fast|fast)
 flags='-A dead_code -A unexpected_cfgs'
 [[ "$mode" == profile-old ]] || flags="$flags --cfg v8_pool_zero"
 [[ "$mode" == fast ]] || flags="$flags --cfg v8_pool_profile"
 scope env CARGO_TARGET_DIR="$ex/performance-sbf/target" RUSTC=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc RUSTFLAGS="$flags" cargo-build-sbf --offline --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 --no-default-features --features v7-pair-forest-one-tx-candidate --manifest-path "$rt/programs/aspis-pool/Cargo.toml" --sbf-out-dir "$rt/sbf-pool-zero-$mode" -- --locked 2>&1 | tee "$log";;
*) exit 2;;
esac
