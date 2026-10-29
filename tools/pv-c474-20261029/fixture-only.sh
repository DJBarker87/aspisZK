#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-pv-c474-20261029
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR="$H/native-target"
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
cd "$H/src"
export CARGO_TARGET_DIR="$H/probe-target"
cargo +1.94.1 test --release --locked --offline -j 4 -p aspis-r1-cost-probe --lib --features optimized-terminal,r1p-check,ct-host-prover RealR1_client::tests -- --test-threads=1 --nocapture
