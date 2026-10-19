#!/bin/sh
# usage: build-driver.sh <receipt-name> <note>
set -e
export CARGO_TARGET_DIR=/home/dombarker/project-offloads/codex-r1-pool-b1-20261019/driver-target CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
cd /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/driver-src/tools/r1-cost-probe
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/harness/capped.py /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/receipts/$1 "$2" -- cargo build --release --locked --offline -j 4 --bin pool_gate --features private-leaf-salts
mkdir -p /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/artifacts
cp /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/driver-target/release/pool_gate /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/artifacts/pool_gate_b1
sha256sum /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/artifacts/pool_gate_b1; stat -c "%n %s" /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/artifacts/pool_gate_b1
