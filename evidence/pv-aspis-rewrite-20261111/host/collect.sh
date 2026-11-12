#!/bin/bash
# Host side: stage the small evidence files of this job under evidence-stage/ (copies; nothing is removed).
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111; S=$W/evidence-stage; cd $W
mkdir -p $S/host-runs $S/gate-d/check $S/gate-d/emitted $S/gates
for r in runs/*/; do n=$(basename $r); mkdir -p $S/host-runs/$n
  for f in receipt.json target.json time.log cgroup.json; do [ -e $r/$f ] && cp $r/$f $S/host-runs/$n/; done
  ls $r | grep -c admission > $S/host-runs/$n/admission_attempts.txt
  case $n in A-*|AF-*|L-*) for f in stdout.log stderr.log; do [ -e $r/$f ] && sed "s/\x1b\[[0-9;]*m//g" $r/$f | head -c 400000 > $S/host-runs/$n/$f; done;; esac
done
for c in check/*/; do n=$(basename $c); mkdir -p $S/gate-d/check/$n; cp $c/RwCheck.lean $S/gate-d/check/$n/; [ -e $c/mkcheck.json ] && cp $c/mkcheck.json $S/gate-d/check/$n/; done
sha256sum llbc/*.llbc > $S/gate-d/llbc.sha256
for e in emit/*/generated; do t=$(basename $(dirname $e)); [ -L emit/$t ] && continue; sha256sum $e/*.lean | sed "s#$W/##" >> $S/gate-d/emissions.sha256; done
cp runs/*.STATUS $S/gate-d/ 2>/dev/null
for t in base base2 base3 after1 final; do [ -d out/$t ] || continue; mkdir -p $S/gates/$t
  cp out/$t/*.txt out/$t/*.sha256 $S/gates/$t/ 2>/dev/null
  if [ -d out/$t/sbf ]; then mkdir -p $S/gates/$t/sbf; cp out/$t/sbf/TABLE.txt out/$t/sbf/source_tree.sha256 $S/gates/$t/sbf/; for p in out/$t/sbf/*/; do q=$S/gates/$t/sbf/$(basename $p); mkdir -p $q; cp $p/cmd.txt $p/env_exact.txt $p/exit $p/time.log $p/so.sha256 $p/so.size $p/lock_before.txt $p/lock_after.txt $q/ 2>/dev/null; done; fi
  if [ -d out/$t/tests ]; then mkdir -p $S/gates/$t/tests; cp out/$t/tests/*.count out/$t/tests/*.failed $S/gates/$t/tests/; for l in out/$t/tests/*.log; do grep -h "^test result\|^running\|FAILED\|panicked" $l > $S/gates/$t/tests/$(basename $l .log).summary; done; fi
done
cp out/timing-*.txt $S/gates/ 2>/dev/null
cp *_chain*.log sync-*.log SOURCE_REVISION $S/ 2>/dev/null
tar -czf evidence-stage.tgz -C $S . && ls -la evidence-stage.tgz && du -sh $S
