#!/bin/sh
# usage: build-sbf.sh <receipt-name> <verifier|verifier-clean|verifier-profiling|pool|pool-clean> <note>
# SBF build from this branch's tree in its own capped scope (Solana 3.1.13
# cargo-build-sbf, --locked, offline, -j 4).
set -e
H=/home/dombarker/project-offloads/codex-cx-stage2b-20261020
export CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
SOL=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
case $2 in
  verifier) M=programs/r1-cost-probe; F=pool-adapter,private-leaf-salts; SO=aspis_r1_cost_probe_program.so; T=$H/sbf-target-verifier;;
  verifier-clean) M=programs/r1-cost-probe; F=pool-adapter,private-leaf-salts; SO=aspis_r1_cost_probe_program.so; T=$H/sbf-target-verifier-clean;;
  verifier-profiling) M=programs/r1-cost-probe; F=pool-adapter,private-leaf-salts,cu-profiling; SO=aspis_r1_cost_probe_program.so; T=$H/sbf-target-verifier-profiling;;
  pool) M=programs/aspis-pool; F=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit; SO=aspis_pool.so; T=$H/sbf-target-pool;;
  pool-clean) M=programs/aspis-pool; F=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit; SO=aspis_pool.so; T=$H/sbf-target-pool-clean;;
esac
O=$H/artifacts/$2; mkdir -p $O
export CARGO_TARGET_DIR=$T
cd $H/src
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 $H/harness-r4/capped.py $H/receipts/r4-$1 "$3" -- $SOL --manifest-path $H/src/$M/Cargo.toml --sbf-out-dir $O --features $F --skip-tools-install --offline -j 4 -- --locked
cp $T/sbpf-solana-solana/release/$SO $O/linked.elf
sha256sum $O/$SO $O/linked.elf
stat -c "%n %s" $O/$SO $O/linked.elf
