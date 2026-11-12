#!/bin/bash
# Host side: stage the small evidence files of the rebase rerun under evidence-stage/ (copies; nothing is removed).
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112; S=$W/evidence-stage; cd $W
mkdir -p $S/host-runs $S/gates
for r in runs/*/; do n=$(basename $r); mkdir -p $S/host-runs/$n
  for f in receipt.json target.json time.log cgroup.json; do [ -e $r/$f ] && cp $r/$f $S/host-runs/$n/; done
  ls $r | grep -c 'admission-.*json' > $S/host-runs/$n/admission_attempts.txt
done
for t in before after; do mkdir -p $S/gates/$t/sbf $S/gates/$t/tests
  cp out/$t/*.txt out/$t/*.sha256 $S/gates/$t/ 2>/dev/null
  cp out/$t/sbf/TABLE.txt out/$t/sbf/*.sha256 out/$t/sbf/tool_version.txt $S/gates/$t/sbf/
  for p in out/$t/sbf/*/; do q=$S/gates/$t/sbf/$(basename $p); mkdir -p $q; cp $p/cmd.txt $p/env_exact.txt $p/exit $p/time.log $p/so.sha256 $p/so.size $p/lock_before.txt $p/lock_after.txt $p/dep_sources.txt $q/ 2>/dev/null; done
  grep -B2 -A12 '^error' out/$t/sbf/aspis-verifier/stderr.log | head -60 > $S/gates/$t/sbf/aspis-verifier/error_excerpt.txt
  cp out/$t/tests/*.count out/$t/tests/*.outcomes out/$t/tests/*.cmd $S/gates/$t/tests/
  for s in core statement prover probe tool; do grep ' \.\.\. FAILED$' out/$t/tests/$s.outcomes > $S/gates/$t/tests/$s.failed_names; grep -h "^test result\|^running\|panicked" out/$t/tests/$s.log > $S/gates/$t/tests/$s.summary; done
done
{ for f in fixture retry fail; do cmp out/before/table-$f.txt out/after/table-$f.txt && echo "table-$f IDENTICAL" || echo "table-$f DIFFERENT"; done
  cmp out/before/sbf/TABLE.txt out/after/sbf/TABLE.txt && echo "ELF TABLE IDENTICAL" || echo "ELF TABLE DIFFERENT"
  for s in core statement prover probe tool; do echo "== $s: before $(cat out/before/tests/$s.count); after $(cat out/after/tests/$s.count)"; diff out/before/tests/$s.outcomes out/after/tests/$s.outcomes; done; } > $S/gates/COMPARE.txt 2>&1
cp out/timing-*.txt $S/gates/ 2>/dev/null
cp chain_*.log timing_wait.log TIMING_* SOURCE_REVISION_* $S/ 2>/dev/null
diff -rq src-before src-after > $S/src_before_vs_after.txt
tar -czf evidence-stage.tgz -C $S . && ls -la evidence-stage.tgz && du -sh $S
