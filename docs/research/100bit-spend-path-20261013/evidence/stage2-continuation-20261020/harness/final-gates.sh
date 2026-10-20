#!/bin/sh
set -eu
export RUSTFLAGS="-C link-arg=-Wl,--threads=4"
H=/home/dombarker/project-offloads/codex-cx-stage2b-20261020
sh $H/harness-continuation/gates.sh codec counter counter-audit
python3 $H/harness-continuation/run-refactor-gates.py
sh $H/harness-continuation/build-sbf.sh sbf-final verifier "Final-source SBF compilation/link; cached dependencies; no proof generation"
mkdir -p $H/stack-continuation/verifier
cp $H/artifacts/verifier/linked.elf $H/stack-continuation/verifier/linked.elf
cp $H/artifacts/verifier/aspis_r1_cost_probe_program.so $H/stack-continuation/verifier/stripped.so
cat $H/receipts/cont-sbf-final/stdout.log $H/receipts/cont-sbf-final/stderr.log > $H/stack-continuation/verifier/build.log
$H/harness-continuation/capped-run.sh strict-stack-final "Complete linked ELF diagnostic classification; seconds" $H -- python3 $H/harness-continuation/strict-stack.py $H/stack-continuation/verifier
python3 $H/harness-continuation/replay-cu.py
sh $H/harness-continuation/gates.sh retry
