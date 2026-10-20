#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-cx-sim-bin-20261020
cd "$H/repo"
# Compilation first; the measured gate's heavy step is P_R1 certificate
# generation/checking, then simulator semantic summation (optimized only).
export RUSTFLAGS='-C link-arg=-Wl,--threads=4'
export CARGO_TARGET_DIR="$H/target"
export PATH="$HOME/.cargo/bin:$PATH"
/usr/bin/time -v -o "$H/time-build.txt" cargo build --release -j 4 -p aspis-r1-cost-probe --features r1p-check --example r1p_sim_gate
/usr/bin/time -v -o "$H/time-tests.txt" cargo test --release -j 4 -p aspis-r1-cost-probe --features r1p-check --lib sim::tests -- --nocapture
/usr/bin/time -v -o "$H/time-gate.txt" "$H/target/release/examples/r1p_sim_gate" 4 "$H/gate.json"
