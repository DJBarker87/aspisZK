#!/bin/bash
# X2d: build the replay tool x2d_pool_replay (a new binary placed in a COPY of the d78cbfaa403 tree, W/x2d/tool-tree,
# tools/r1-cost-probe/src/bin/x2d_pool_replay.rs; no existing tool source is changed) with the tool recipe of the
# lead's scripts (cargo +1.94.1, release, offline, locked, 4 jobs). Own target directory W/x2d/target/native-tool.
# Runs INSIDE one fv_slot.sh scope. Time is expected in compilation (cold target directory).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
cd $W/x2d/tool-tree/tools/r1-cost-probe
taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/x2d/target/native-tool CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 cargo +1.94.1 build --release --offline --locked --bin x2d_pool_replay
rc=$?
[ $rc = 0 ] && cp $W/x2d/target/native-tool/release/x2d_pool_replay $W/x2d/bin/x2d_pool_replay && sha256sum $W/x2d/bin/x2d_pool_replay $W/x2d/tool-tree/tools/r1-cost-probe/src/bin/x2d_pool_replay.rs
exit $rc
