#!/bin/sh
# usage: build-sbf.sh <receipt-name> <target-dir> <out-dir> <note>
set -e
cd /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/src
export CARGO_TARGET_DIR=$2 CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
SOL=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
mkdir -p $3
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/harness/capped.py /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/receipts/$1 "$4" -- $SOL --manifest-path /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/src/programs/aspis-pool/Cargo.toml --sbf-out-dir $3 --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit --skip-tools-install --offline -j 4 -- --locked
cp $2/sbpf-solana-solana/release/aspis_pool.so $3/linked.elf
sha256sum $3/aspis_pool.so $3/linked.elf
stat -c "%n %s" $3/aspis_pool.so $3/linked.elf
