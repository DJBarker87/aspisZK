#!/bin/bash
# Second baseline chain (base revision plus the gate tool's fail mode and the test input files that the
# first chain lacked). The first table run was cut by its timeout on a loaded host; the test suites
# core, prover, probe and tool had not compiled for want of input files outside the first source copy.
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
cd $W; J="bash $W/tools/job.sh"
$J B-base2-native 3600 "optimized build of pv_bytes_gate (with fail mode) at the base revision; time expected in compilation" bash $W/tools/native_build.sh base2
$J G-base2-table 7200 "gate B fixture table, base, seeds 1..16; time expected in proof generation (release binary)" bash $W/tools/table.sh base2 fixture table 1 16
$J G-base2-retry 7200 "gate B retry rows, base, seeds 17..20; time expected in proof generation (release binary)" bash $W/tools/table.sh base2 retry retry 17 4
$J G-base2-fail 7200 "gate B forced failing paths, base, seeds 1..2; time expected in proof generation (release binary)" bash $W/tools/table.sh base2 fail fail 1 2
for s in core prover probe tool; do
  $J T-base2-$s 5400 "cargo test --release, suite $s, base revision; time expected in compilation then tests" bash $W/tools/tests.sh base2 $s
done
echo done > $W/BASE2_CHAIN_DONE
