#!/bin/sh
# Build the screen probe for SBF and run every fixture five times.
# Run on the build host from the uploaded screen directory:
#   sh run_on_build_host.sh build   (12G/16G, no swap)
#   sh run_on_build_host.sh run     (2G/3G, no swap)
set -eu
BASE=$(cd "$(dirname "$0")" && pwd)
SOL=/home/dombarker/.local/share/solana/install/active_release/bin
DRIVER=/home/dombarker/project-offloads/aspis-r101-auth-20260930-a/r101-driver
case "$1" in
build)
  cp -n /home/dombarker/project-offloads/aspis-r101-auth-20260930-a/docs/research/v8-no-work-100-20260907/experiments/performance-sbf/Cargo.lock "$BASE/probe/Cargo.lock"
  exec systemd-run --user --wait --collect --pipe --quiet -p MemoryHigh=12G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=128 \
    env NO_DNA=1 PATH=/home/dombarker/.cargo/bin:$SOL:/usr/bin:/bin \
        RUSTC=/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc \
        CARGO_TARGET_DIR="$BASE/target" \
    /usr/bin/time -v "$SOL/cargo-build-sbf" --offline --skip-tools-install --no-rustup-override \
        --tools-version v1.54 --jobs 2 --manifest-path "$BASE/probe/Cargo.toml" --sbf-out-dir "$BASE/elf"
  ;;
run)
  exec systemd-run --user --wait --collect --pipe --quiet -p MemoryHigh=2G -p MemoryMax=3G -p MemorySwapMax=0 -p TasksMax=64 \
    sh -c 'for f in "$0"/fixtures/*; do for k in 1 2 3 4 5; do printf "%s " "$(basename "$f")"; "$1" "$0/elf/aspis_wide_field_screen_probe.so" "$f" | grep "^{" ; done; done' "$BASE" "$DRIVER"
  ;;
esac
