#!/bin/bash
# Runs INSIDE a scope (fv_slot.sh). Aspis freeze: optimized host build of the devnet client with the
# prover (features r1p-check) from a named source tree, then its planner tests. fv_client_build.sh
# with the source tree as a parameter and an own target directory per tree.
# Usage: fv_frz_client.sh <attempt> <source-dir-name>
# Time is expected in compilation.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; S=$2
OUT=$W/out/$A; test ! -e $OUT || { echo "exists: $OUT"; exit 2; }
mkdir -p $OUT
cd $W/$S/tools/r1-cost-probe
E=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
   CARGO_TARGET_DIR=$W/target/native-client-bin-$S CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4)
printf '%s\n' "${E[@]}" > $OUT/env_exact.txt
taskset --cpu-list 0-3 env -i "${E[@]}" cargo +1.94.1 build --release --offline --locked --features r1p-check --bin devnet_spend || exit 1
cp $W/target/native-client-bin-$S/release/devnet_spend $OUT/devnet_spend
sha256sum $OUT/devnet_spend | tee $OUT/client.sha256
taskset --cpu-list 0-3 env -i "${E[@]}" cargo +1.94.1 test --release --offline --locked --features r1p-check --bin devnet_spend
