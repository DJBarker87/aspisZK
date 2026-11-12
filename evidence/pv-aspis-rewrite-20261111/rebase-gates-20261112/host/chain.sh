#!/bin/bash
# One tree's chain, one scope at a time: gate A (SBF builds), the gate tool, gate B (three tables),
# the five test suites. Usage: chain.sh <tag> <src-dir-name> <revision-label> <cpu-list>
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112
T=$1; S=$2; export PV_SRC_REV=$3; C=$4; cd $W; J="bash $W/tools/job.sh"
$J B-$T-sbf 5400 "SBF builds of the six program targets, tree $T; time expected in compilation" bash $W/tools/sbf_all.sh $T $S $C
$J B-$T-native 3600 "optimized build of pv_bytes_gate, tree $T; time expected in compilation" bash $W/tools/native_build.sh $T $S $C
$J G-$T-table 7200 "gate B fixture table, tree $T, seeds 1..16; time expected in proof generation (release binary)" bash $W/tools/table.sh $T fixture table 1 16
$J G-$T-retry 7200 "gate B retry rows, tree $T, seeds 17..20; time expected in proof generation (release binary)" bash $W/tools/table.sh $T retry retry 17 4
$J G-$T-fail 7200 "gate B forced failing paths, tree $T, seeds 1..2; time expected in proof generation (release binary)" bash $W/tools/table.sh $T fail fail 1 2
for s in core statement prover probe tool; do
  $J T-$T-$s 5400 "cargo test --release, suite $s, tree $T; time expected in compilation then tests" bash $W/tools/tests.sh $T $S $C $s
done
echo done > $W/CHAIN_$T.DONE
