#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-pv-c474-20261029
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR="$H/native-target"
export RUSTFLAGS='-C link-arg=-Wl,--threads=4'
unset CARGO_ENCODED_RUSTFLAGS
cd "$H/src/tools/r1-cost-probe-base"
cargo build --release --locked --offline -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend --bin pv_client_gate
