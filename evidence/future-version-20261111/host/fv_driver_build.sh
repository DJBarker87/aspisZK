#!/bin/bash
# Runs INSIDE a scope. Optimized host build of the LiteSVM driver (time expected in compilation).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
cd $W/src/tools/r1-cost-probe
sha256sum Cargo.lock > $W/out/driver_lock_before.txt
taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo \
  CARGO_TARGET_DIR=$W/target/native CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 \
  cargo +1.94.1 build --release --offline --locked --bin fused_probe --bin one_tx_replay
rc=$?
sha256sum Cargo.lock > $W/out/driver_lock_after.txt
sha256sum $W/target/native/release/fused_probe > $W/out/driver.sha256 2>/dev/null
exit $rc
