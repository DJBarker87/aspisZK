#!/bin/sh
# usage: capped-run.sh <receipt-name> <expected-time-note> <workdir> -- cmd...
# One command in its own systemd scope (MemoryHigh 6G, MemoryMax 8G, no swap,
# TasksMax 64), receipt via capped.py (refuses an existing receipt dir).
set -e
H=/home/dombarker/project-offloads/codex-r1-proof-size-20261019
R=$1; N=$2; W=$3; shift 4
export CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
export RUSTFLAGS="${RUSTFLAGS:--C link-arg=-Wl,--threads=4}"
cd $W
exec systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 $H/harness/capped.py $H/receipts/$R "$N" -- "$@"
