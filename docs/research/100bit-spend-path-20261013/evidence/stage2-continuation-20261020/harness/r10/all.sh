#!/bin/sh
set -eu
export RUSTFLAGS="-C link-arg=-Wl,--threads=4"
H=/home/dombarker/project-offloads/codex-cx-stage2b-20261020
export CARGO_TARGET_SBPF_SOLANA_SOLANA_LINKER=$H/harness-r10/sbf-linker/rust-lld
sh $H/harness-r10/build-sbf.sh sbf-final verifier "SBF compilation/link after query ABI optimization; cached dependencies"
mkdir -p $H/stack-r10/verifier
cp $H/artifacts/verifier/linked.elf $H/stack-r10/verifier/linked.elf
cp $H/artifacts/verifier/aspis_r1_cost_probe_program.so $H/stack-r10/verifier/stripped.so
cat $H/receipts/r10-sbf-final/stdout.log $H/receipts/r10-sbf-final/stderr.log > $H/stack-r10/verifier/build.log
$H/harness-r10/capped-run.sh strict-stack-final "Complete linked ELF stack audit" $H -- python3 $H/harness-r10/strict-stack.py $H/stack-r10/verifier
python3 $H/harness-r10/replay-cu.py
sh $H/harness-r10/gates.sh codec counter counter-audit
python3 $H/harness-r10/run-refactor-gates.py
sh $H/harness-r10/gates.sh retry
