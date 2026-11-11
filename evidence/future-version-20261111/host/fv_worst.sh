#!/bin/bash
# Worst-case compute: build tools/r1-cost-probe/src/bin/one_tx_worst.rs in the head tree (src) with
# its own target directory, then run it over the scenario list against the A6, X1 and X2 ELFs.
# Usage: fv_worst.sh <tag> <specs>
# Expected time: compilation first (a cold native build of the tool crate and the prover, own target
# directory), then about one proof per scenario (tens of seconds each) and a few seconds per run.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
TAG=$1; SPECS=$2
D=$W/WORST_$TAG.done; rm -f $D
mkdir -p worst
B=$W/worst/one_tx_worst-src
if [ ! -x $B ]; then
  cp $W/one_tx_worst.rs $W/src/tools/r1-cost-probe/src/bin/one_tx_worst.rs
  bash fv_slot.sh WC-build-$TAG 3000 bash -c "cd $W/src/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-wc-src CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-src/release/one_tx_worst $B" || { echo BUILD_FAILED > $D; exit 1; }
fi
bash fv_slot.sh WC-run-$TAG 5400 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION) taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/worst/$TAG.json '$SPECS' A6=$W/out/A6-onetx-head/artifacts/aspis_r1_cost_probe_program.so X1=$W/out/X1-rewrites/artifacts/aspis_r1_cost_probe_program.so X2=$W/out/X2-rewrites-hashv/artifacts/aspis_r1_cost_probe_program.so"
echo "run exit $?" > $D
sha256sum $B $W/one_tx_worst.rs $W/worst/$TAG.json >> $D 2>&1
