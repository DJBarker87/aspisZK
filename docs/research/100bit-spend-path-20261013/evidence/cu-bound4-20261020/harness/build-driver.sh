#!/bin/sh
# usage: build-driver.sh <receipt-name> <sweep|trace> <note> [extra cargo args]
# Driver source is the retained bound3 harness, rebuilt against the frozen source.
set -e
H=/home/dombarker/project-offloads/codex-cx-cu-bound4-20261020
R=$1; V=$2; N=$3; shift 3
case $V in
  sweep) D=$H/src/tools/r1-cost-probe-sweep; F=private-leaf-salts; T=$H/driver-target; A=pool_gate;;
  trace) D=$H/src/tools/r1-cost-probe-sweep-trace; F=private-leaf-salts,trace; T=$H/driver-target-trace; A=pool_gate_trace;;
esac
export CARGO_TARGET_DIR=$T CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
# TasksMax=64: rust-lld spawns one thread per core (22) per link; cap its threads so
# four parallel links stay inside the scope (first attempt aborted: EAGAIN in lld).
export RUSTFLAGS="-C link-arg=-Wl,--threads=4"
cd $D
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 $H/harness/capped.py $H/receipts/$R "$N" -- cargo build --release --offline -j 4 --bin pool_gate --features $F "$@"
cp $T/release/pool_gate $H/artifacts/$A
sha256sum $H/artifacts/$A; stat -c "%n %s" $H/artifacts/$A
