#!/bin/sh
# usage: test-wallet.sh <receipt-name> <note> [cargo test args...]
cd /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/src/crates/aspis-pool-wallet-v1
export CARGO_TARGET_DIR=/home/dombarker/project-offloads/codex-r1-pool-b1-20261019/wallet-target CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
R=$1; N=$2; shift 2
exec systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/harness/capped.py /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/receipts/$R "$N" -- /home/dombarker/.cargo/bin/cargo test --release --offline --locked -j ${JOBS:-4} "$@"
