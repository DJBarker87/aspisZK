#!/usr/bin/env bash
set -euo pipefail
expected_r18=4be52794cdacec884686a9d860285cc226e94d12eeaa95b707ebb761171f9372
actual_r18=$(sha256sum src/r18_sparse_coded_g.rs | cut -d' ' -f1)
test "$actual_r18" = "$expected_r18"
export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_PROFILE_RELEASE_OPT_LEVEL=3
export CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
export CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
cargo build -vv --offline --locked --release --jobs 1 --bin r724_h1_projected_residual_probe > build.log 2>&1
./target/release/r724_h1_projected_residual_probe semantic-scan > semantic-scan.log 2>&1
