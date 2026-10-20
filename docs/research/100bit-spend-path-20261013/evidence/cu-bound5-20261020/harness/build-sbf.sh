#!/bin/sh
# usage: build-sbf.sh <receipt-name> <program: pool|verifier|verifier-profiling> <note>
# Builds one SBF program from the exact candidate c16e59e77 source in its own capped scope.
# DEBUGLINES=1: line-tables-only build into a separate target/out dir, used only to map
# .text slots to source lines (its .text must equal the deployed build, checked by cmp).
set -e
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
cd $H/src
export CARGO_HOME=/home/dombarker/.cargo PATH=$H/harness/linker-bin:/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
SOL=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
case $2 in
  pool) M=programs/aspis-pool; F=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit; SO=aspis_pool.so; T=$H/sbf-target-pool;;
  verifier) M=programs/r1-cost-probe; F=pool-adapter,private-leaf-salts; SO=aspis_r1_cost_probe_program.so; T=$H/sbf-target-verifier;;
  verifier-devnet) M=programs/r1-cost-probe; F=pool-adapter,private-leaf-salts; SO=aspis_r1_cost_probe_program.so; T=$H/sbf-target-verifier-devnet
    export ASPIS_R1_POOL_PROGRAM_ID=$(jq -er .programs.pool "$H/r1-devnet.template.json")
    export ASPIS_R1_REGISTRY_PROGRAM_ID=$(jq -er .programs.registry "$H/r1-devnet.template.json");;
  verifier-profiling) M=programs/r1-cost-probe; F=pool-adapter,private-leaf-salts,cu-profiling; SO=aspis_r1_cost_probe_program.so; T=$H/sbf-target-verifier-profiling;;
esac
O=$H/artifacts/$2
if [ "$DEBUGLINES" = 1 ]; then export CARGO_PROFILE_RELEASE_DEBUG=line-tables-only CARGO_PROFILE_RELEASE_STRIP=none; T=$T-debuglines; O=$O-debuglines; fi
# SBF invokes rust-lld directly (its default is --threads=1); -Wl is
# exclusively for native cc linking. Passing -Wl to SBF failed, receipt retained.
unset RUSTFLAGS
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C link-arg=-Wl,--threads=4"
export CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS="-C link-arg=--threads=4"
export CARGO_TARGET_DIR=$T; mkdir -p $O
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 $H/harness/capped.py $H/receipts/$1 "$3" -- $SOL --manifest-path $H/src/$M/Cargo.toml --sbf-out-dir $O --features $F --skip-tools-install --offline -j 4 -- --locked
cp $T/sbpf-solana-solana/release/$SO $O/linked.elf
sha256sum $O/$SO $O/linked.elf
stat -c "%n %s" $O/$SO $O/linked.elf
