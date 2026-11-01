#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-pv-c474-20261029
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR="$H/native-target"
export RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
unset CARGO_ENCODED_RUSTFLAGS RUSTC_BOOTSTRAP
cd "$H/src/tools/r1-cost-probe"
cargo +1.94.1 test --release --locked --offline -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend -- --test-threads=1
python3 "$H/bundle/fixed-fixtures.py"
python3 "$H/bundle/ct-and-signing.py"
"$H/artifacts/pv_client_gate" "$H/native-target/client/devnet_spend" "$H/bundle/elf-default-affinity4/aspis_r1_cost_probe_program.so" "$H/bundle/elf-devnet/aspis_r1_cost_probe_program.so" "$H/bundle/elf-pool/aspis_pool.so" "$H/bundle/runtime-private"
