#!/bin/sh
# usage: build-sbf.sh <receipt-name> <shipped|candidate> <note>
# SBF build of the R1 verifier program from this branch's tree, capped scope.
set -e
H=/home/dombarker/project-offloads/codex-r1-proof-size-20261019
export CARGO_HOME=/home/dombarker/.cargo PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_NET_OFFLINE=true
SOL=/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf
case $2 in
  shipped) F=pool-adapter,private-leaf-salts; T=$H/sbf-target-shipped;;
  shipped-final) F=pool-adapter,private-leaf-salts; T=$H/sbf-target-shipped-final;;
  candidate) F=pool-adapter,compact-binary; T=$H/sbf-target-candidate;;
  candidate-clean) F=pool-adapter,compact-binary; T=$H/sbf-target-candidate-clean;;
  candidate-profiling) F=pool-adapter,compact-binary,cu-profiling; T=$H/sbf-target-candidate-profiling;;
esac
O=$H/artifacts/verifier-$2; mkdir -p $O
export CARGO_TARGET_DIR=$T
cd $H/src
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 $H/harness/capped.py $H/receipts/$1 "$3" -- $SOL --manifest-path $H/src/programs/r1-cost-probe/Cargo.toml --sbf-out-dir $O --features $F --skip-tools-install --offline -j 4 -- --locked
cp $T/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so $O/linked.elf
sha256sum $O/aspis_r1_cost_probe_program.so $O/linked.elf
stat -c "%n %s" $O/aspis_r1_cost_probe_program.so $O/linked.elf
