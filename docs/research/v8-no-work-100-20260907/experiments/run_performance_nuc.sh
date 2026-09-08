#!/usr/bin/env bash
# Run on the authorised NUC, in this task's isolated source copy. No RPC.
set -euo pipefail
[[ $# == 1 && "$1" == /* && ! -e "$1" ]] || { echo "usage: bash run_performance_nuc.sh NEW_ABSOLUTE_OUTPUT_DIR" >&2; exit 2; }
readonly perf_out="$1"
readonly perf_exp="$(cd "$(dirname "$0")" && pwd)"
readonly perf_tools=/home/dombarker/.cache/solana/v1.54/platform-tools
readonly perf_path=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
[[ "$(uname -m)" == x86_64 && "$(uname -s)" == Linux && -x "$perf_tools/rust/bin/rustc" ]]
mkdir "$perf_out"
readonly perf_unit="aspis-v8-perf-$(date +%s)-$$"
scope() {
  local suffix="$1"; shift
  systemd-run --user --scope --unit="$perf_unit-$suffix" \
    -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 \
    /usr/bin/time -v env NO_DNA=1 PATH="$perf_path" "$@"
}
scope host-build env RUSTFLAGS="--cfg v8_payment_extraction --cfg v8_performance --cfg v8_performance_fast -A dead_code -A unexpected_cfgs" \
  cargo build --offline --locked --release --jobs 2 --features insecure-spend-fixture,selected-v7-kernels \
  --manifest-path "$perf_exp/performance-host/Cargo.toml" 2>&1 | tee "$perf_out/host-build.log"
scope sbf-build env RUSTC="$perf_tools/rust/bin/rustc" RUSTFLAGS="--cfg v8_performance_sbf --cfg v8_performance_fast -A dead_code -A unexpected_cfgs" \
  cargo-build-sbf --offline --skip-tools-install --no-rustup-override --tools-version v1.54 --jobs 2 \
  --features selected-v7-kernels --manifest-path "$perf_exp/performance-sbf/Cargo.toml" \
  --sbf-out-dir "$perf_out/sbf" -- --locked 2>&1 | tee "$perf_out/sbf-build.log"
if rg -q 'overflows the maximum allowed frame|Stack offset.*exceeded|Error:' "$perf_out/sbf-build.log"; then
  echo "SBF compiler diagnostic: do not treat cargo exit 0 as a valid stack gate" >&2; exit 1
fi
scope svm-build cargo build --offline --locked --release --jobs 2 \
  --manifest-path "$perf_exp/performance-svm/Cargo.toml" 2>&1 | tee "$perf_out/svm-build.log"
# No concurrent build contaminates these phase timings.
scope host "$perf_exp/performance-host/target/release/aspis-v8-performance-host" "$perf_out/fixtures" \
  2>&1 | tee "$perf_out/host.log"
scope svm "$perf_exp/performance-svm/target/release/aspis-v8-performance-svm" \
  "$perf_out/sbf/aspis_v8_performance_sbf.so" "$perf_out/fixtures" 2>&1 | tee "$perf_out/svm.log"
sha256sum "$perf_out/sbf/aspis_v8_performance_sbf.so" "$perf_out/fixtures/proof-1.bin" \
  "$perf_out/fixtures/proof-2.bin" "$perf_out/fixtures/proof-3.bin" | tee "$perf_out/artifacts.sha256"
