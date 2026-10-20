#!/usr/bin/env bash
set -euo pipefail
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$PWD/sbf-target-carrier CARGO_NET_OFFLINE=true
export CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4'
env -u RUSTFLAGS /home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf --manifest-path "$PWD/src/tools/r1-buffer-carrier/Cargo.toml" --sbf-out-dir "$PWD/artifacts/carrier" --skip-tools-install --offline -j 4
sha256sum artifacts/carrier/aspis_r1_buffer_carrier.so
