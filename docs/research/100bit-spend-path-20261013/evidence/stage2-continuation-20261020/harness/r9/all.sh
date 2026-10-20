#!/bin/sh
set -eu
export RUSTFLAGS="-C link-arg=-Wl,--threads=4"
H=/home/dombarker/project-offloads/codex-cx-stage2b-20261020
export CARGO_TARGET_SBPF_SOLANA_SOLANA_LINKER=$H/harness-r9/sbf-linker/rust-lld
sh $H/harness-r9/build-sbf.sh sbf-final verifier "SBF compilation/link after query ABI optimization; cached dependencies"
mkdir -p $H/stack-r9/verifier
cp $H/artifacts/verifier/linked.elf $H/stack-r9/verifier/linked.elf
cp $H/artifacts/verifier/aspis_r1_cost_probe_program.so $H/stack-r9/verifier/stripped.so
cat $H/receipts/r9-sbf-final/stdout.log $H/receipts/r9-sbf-final/stderr.log > $H/stack-r9/verifier/build.log
$H/harness-r9/capped-run.sh strict-stack-final "Complete linked ELF stack audit" $H -- python3 $H/harness-r9/strict-stack.py $H/stack-r9/verifier
python3 $H/harness-r9/replay-cu.py
sh $H/harness-r9/gates.sh codec counter counter-audit
python3 $H/harness-r9/run-refactor-gates.py
sh $H/harness-r9/gates.sh retry
