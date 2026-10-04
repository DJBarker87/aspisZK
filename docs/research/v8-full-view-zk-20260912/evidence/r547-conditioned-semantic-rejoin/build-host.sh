#!/usr/bin/env bash
set -euo pipefail
root=/home/dombarker/project-offloads/aspis-r117-semantic-rejoin-20261004-a
ex="$root/docs/research/v8-no-work-100-20260907/experiments"
evidence="$root/semantic-rejoin-evidence"
mkdir -p "$evidence"
export PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin
SECONDS=0
finish() { status=$?; trap - EXIT; echo "script_exit=$status wall_seconds=$SECONDS"; exit "$status"; }
trap finish EXIT
exec > >(tee "$evidence/build-0004.log") 2>&1
echo "utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "source_revision=6677d5f1310ff7373301fbd79f186278f772e68a"
echo "source_root=$root"
echo "target=aspis-v8-performance-host"
echo "build_stage=compile only; performance/generation in separate authorized run"
echo "lean_not_applicable=true"
uname -a
rustc --version
cargo --version
sha256sum "$evidence/selected-rustflags.txt" \
  "$ex/relation_callback.rs" "$ex/payment_extraction.rs" \
  "$ex/performance.rs" "$ex/semantic_rejoin_oracle.rs"
grep -E 'MemAvailable|SwapFree' /proc/meminfo
free -h
systemd-cgls --user --no-pager | rg -n 'aspis-|lean|cargo|rustc' || true
flags="$(cat "$evidence/selected-rustflags.txt") --cfg v8_semantic_rejoin"
unit="aspis-v8-semantic-rejoin-build-$(date +%s)-$$"
echo "unit=$unit MemoryHigh=5G MemoryMax=7G MemorySwapMax=0 TasksMax=128"
printf 'RUSTFLAGS=%s\n' "$flags"
printf 'command=cargo build -vv --offline --locked --release --jobs 1 --features insecure-spend-fixture,selected-v7-kernels --manifest-path %s/performance-host/Cargo.toml --bin aspis-v8-performance-host\n' "$ex"
systemd-run --user --wait --collect --pipe --unit="$unit" \
  --working-directory="$ex" \
  -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v env NO_DNA=1 \
    PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin \
    RUSTFLAGS="$flags" CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true \
    CARGO_TARGET_DIR="$ex/performance-host/target" \
    cargo build -vv --offline --locked --release --jobs 1 \
      --features insecure-spend-fixture,selected-v7-kernels \
      --manifest-path "$ex/performance-host/Cargo.toml" \
      --bin aspis-v8-performance-host
echo "build_exit=0"
