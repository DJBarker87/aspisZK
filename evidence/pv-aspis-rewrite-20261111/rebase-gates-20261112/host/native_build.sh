#!/bin/bash
# Runs INSIDE one capped scope. Usage: native_build.sh <tag> <src-dir-name> <cpu-list>
# Optimized host build of the gate tool pv_bytes_gate with the client's feature (r1p-check), from
# the client manifest tools/r1-cost-probe (its own workspace and lock file), toolchain 1.94.1,
# offline, locked, -j 4. The binary is copied to out/<tag>/pv_bytes_gate. Time expected in compilation.
set -u
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112
TAG=$1; S=$2; CPUS=$3; OUT=$W/out/$TAG; mkdir -p $OUT
test ! -e $OUT/pv_bytes_gate || { echo "exists"; exit 2; }
E=(HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo
   CARGO_TARGET_DIR=$W/target/$TAG/native CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4)
cd $W/$S/tools/r1-cost-probe
sha256sum Cargo.lock > $OUT/native_lock_before.txt
taskset --cpu-list $CPUS env -i "${E[@]}" cargo +1.94.1 build --release --offline --locked --features r1p-check --bin pv_bytes_gate || exit 1
sha256sum Cargo.lock > $OUT/native_lock_after.txt
cp $W/target/$TAG/native/release/pv_bytes_gate $OUT/pv_bytes_gate
sha256sum $OUT/pv_bytes_gate > $OUT/pv_bytes_gate.sha256
cat $OUT/pv_bytes_gate.sha256
