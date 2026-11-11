#!/bin/bash
# Runs INSIDE a scope. Optimized host build of the devnet client with the prover
# (features r1p-check), then its planner tests. Time expected in compilation.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
cd $W/src/tools/r1-cost-probe
E=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
   CARGO_TARGET_DIR=$W/target/native CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4)
taskset --cpu-list 0-3 env -i "${E[@]}" cargo +1.94.1 build --release --offline --locked --features r1p-check --bin devnet_spend || exit 1
sha256sum $W/target/native/release/devnet_spend > $W/out/client.sha256
taskset --cpu-list 0-3 env -i "${E[@]}" cargo +1.94.1 test --release --offline --locked --features r1p-check --bin devnet_spend
