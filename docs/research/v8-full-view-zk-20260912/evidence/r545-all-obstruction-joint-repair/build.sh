#!/usr/bin/env bash
set -euo pipefail
cd /home/dombarker/project-offloads/aspis-r117-joint-privacy-schur-20261004-a
export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
export RUSTFLAGS="$(cat rustflags.txt)"
cargo build -vv --offline --locked --release --jobs 1 --manifest-path docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml --bin aspis-v8-performance-host --features insecure-spend-fixture,selected-v7-kernels
