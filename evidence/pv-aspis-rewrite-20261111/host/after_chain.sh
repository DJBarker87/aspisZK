#!/bin/bash
# After chain: waits for the second baseline chain, copies the rewritten crates into the baseline source
# directory (same path as the baseline builds, cargo target directories reused), then runs gates A, B, C and
# the test suites on the rewritten tree. usage: after_chain.sh <tag> <revision-label>
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
T=$1; cd $W; J="bash $W/tools/job.sh"
until [ -e $W/BASE2_CHAIN_DONE ]; do sleep 20; done
rsync -rlc --itemize-changes src-rw/crates/ src/crates/ > sync-$T.log 2>&1
diff -rq src/crates src-rw/crates >> sync-$T.log 2>&1; echo "diff exit $?" >> sync-$T.log
echo "$2" > $W/SOURCE_REVISION
$J B-$T-sbf 5400 "SBF builds of the six program targets on the rewritten tree; time expected in compilation" bash $W/tools/sbf_all.sh $T
$J B-$T-native 3600 "optimized build of pv_bytes_gate on the rewritten tree; time expected in compilation" bash $W/tools/native_build.sh $T
$J G-$T-table 7200 "gate B fixture table, rewritten tree, seeds 1..16; time expected in proof generation (release binary)" bash $W/tools/table.sh $T fixture table 1 16
$J G-$T-retry 7200 "gate B retry rows, rewritten tree, seeds 17..20; time expected in proof generation (release binary)" bash $W/tools/table.sh $T retry retry 17 4
$J G-$T-fail 7200 "gate B forced failing paths, rewritten tree, seeds 1..2; time expected in proof generation (release binary)" bash $W/tools/table.sh $T fail fail 1 2
$J G-$T-timing 7200 "gate C: fixture prover wall time, base2 and $T binaries interleaved, 5 rounds; time expected in proof generation (release binaries)" bash $W/tools/timing.sh $T 5 3 base2 $T
for s in core statement prover probe tool; do
  $J T-$T-$s 5400 "cargo test --release, suite $s, rewritten tree; time expected in compilation then tests" bash $W/tools/tests.sh $T $s
done
{ for f in fixture retry fail; do cmp $W/out/base2/table-$f.txt $W/out/$T/table-$f.txt && echo "table-$f IDENTICAL" || echo "table-$f DIFFERENT"; done
  diff <(cut -d' ' -f1 $W/out/base/sbf/TABLE.txt; cut -d' ' -f5- $W/out/base/sbf/TABLE.txt) <(cut -d' ' -f1 $W/out/$T/sbf/TABLE.txt; cut -d' ' -f5- $W/out/$T/sbf/TABLE.txt) && echo "ELF TABLE IDENTICAL" || echo "ELF TABLE DIFFERENT"; } > $W/out/$T/COMPARE.txt 2>&1
echo done > $W/AFTER_CHAIN_$T.DONE
