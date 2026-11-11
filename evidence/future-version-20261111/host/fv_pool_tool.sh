#!/bin/bash
# Pool page zero check: build the extended one_tx_worst tool (negative scenarios, post-state hashes)
# in its own tree src-pool-tool (a copy of src-xp1 with the tool source at pool-stage/one_tx_worst.rs)
# and its own target directory. Usage: fv_pool_tool.sh
# Time is expected in compilation: a cold native release build of the tool crate and the prover.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
T=src-pool-tool
if [ ! -d $T ]; then cp -a src-xp1 $T; fi
cp pool-stage/one_tx_worst.rs $T/tools/r1-cost-probe/src/bin/one_tx_worst.rs
mkdir -p pool-worst
bash fv_slot.sh PL-tool-build 3000 bash -c "cd $W/$T/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-wc-$T CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-$T/release/one_tx_worst $W/pool-worst/one_tx_worst-pool"
echo "tool build exit $?"
sha256sum pool-stage/one_tx_worst.rs pool-worst/one_tx_worst-pool
