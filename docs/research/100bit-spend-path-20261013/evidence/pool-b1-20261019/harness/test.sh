#!/bin/sh
# usage: test.sh <receipt-name> <note> [cargo test args...]
B=/home/dombarker/project-offloads/codex-r1-pool-b1-20261019
cd $B/src
export CARGO_TARGET_DIR=$B/native-target CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
R=$1; N=$2; shift 2
exec systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 $B/harness/capped.py $B/receipts/$R "$N" -- /home/dombarker/.cargo/bin/cargo test --release --offline --locked -j 4 -p aspis-pool "$@"
