#!/bin/bash
# Runs INSIDE a scope. Optimized host build of the register-trace driver (time expected in compilation).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
cd $W/src/tools/fused-trace
taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo \
  CARGO_TARGET_DIR=$W/target/trace CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 \
  cargo +1.94.1 build --release --offline
rc=$?
sha256sum Cargo.lock > $W/out/trace_driver_lock.txt
sha256sum $W/target/trace/release/aspis-fused-trace > $W/out/trace_driver.sha256 2>/dev/null
exit $rc
