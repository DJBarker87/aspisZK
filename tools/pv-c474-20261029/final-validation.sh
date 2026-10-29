#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-pv-c474-20261029
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR="$H/native-target"
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
cd "$H/src/tools/r1-cost-probe"
cargo test --release --locked --offline -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend -- --test-threads=1
cd "$H"
python3 diagnostics-test.py
"$H/native-target/release/pv_client_gate" "$H/native-target/client/devnet_spend" "$H/elf-default/aspis_r1_cost_probe_program.so" "$H/elf-devnet/aspis_r1_cost_probe_program.so" "$H/elf-pool/aspis_pool.so" "$H/runtime-private-final"
python3 audit.py
