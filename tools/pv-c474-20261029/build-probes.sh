#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-pv-c474-20261029
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR="$H/probe-target"
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" -C panic=abort -C link-arg=-Wl,--threads=4'
unset CARGO_ENCODED_RUSTFLAGS
cd "$H/src"
cargo +1.94.1 build --release --locked --offline -j 4 -p aspis-r1-cost-probe --example prover_rw_differential --example prover_rw_gate --features optimized-terminal,r1p-check,ct-host-prover
