#!/bin/bash
# Runs INSIDE a slot. Build the destination-redirect replay tool from the host source tree (crates
# at the devnet verifier's source, so the re-packed proof matches the deployed format) and run it
# against the deployed one-transaction verifier ELF (A5) and the deployed Pool ELF.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
cd $W/src/tools/r1-cost-probe
taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo \
  CARGO_TARGET_DIR=$W/target/native CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 \
  cargo +1.94.1 build --release --offline --locked --bin one_tx_redirect || exit 1
sha256sum $W/target/native/release/one_tx_redirect
mkdir -p $W/replays-redirect
ASPIS_SOURCE_REVISION="crates and programs at 8a4059c8bc2 (host tree); tool one_tx_redirect.rs from the branch head" \
  $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/out/A5-onetx-lean/artifacts/aspis_r1_cost_probe_program.so $W/replays-redirect/$1.json
