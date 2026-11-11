#!/bin/bash
# Coherent rebuild of the Aspis proof layer. Runs INSIDE one scope (fv_slot.sh).
# Usage: fv_replay_aspis.sh <tag> [exclude-substring ...]
# Every module in $W/replay-<tag>/src (the committed lean directory at the commit named in
# SOURCE_COMMIT) is compiled once, in import order, into a NEW object directory, against R1's L187
# release objects by reference (read only). No object from lean-out is used, so each module is
# built against the objects of this same run. Stops at the first failure.
# Expected time: compilation only, a few seconds per module.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
SYS=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
TAG=$1; shift
R=$W/replay-$TAG; SRC=$R/src; OUT=$R/out
test -d $SRC || { echo "no source dir $SRC"; exit 2; }
test ! -e $OUT || { echo "object dir exists: $OUT (use a new tag)"; exit 2; }
mkdir -p $OUT $R/logs
python3 $W/fv_replay_order.py $SRC "$@" > $R/order.txt 2> $R/skipped.txt || { echo ORDER_FAILED > $R/DONE; exit 3; }
: > $R/manifest.tsv
date -u +%FT%TZ > $R/started
while read M; do
  s=$(sha256sum $SRC/$M.lean | cut -d' ' -f1)
  /usr/bin/time -f "%e %M" -o $R/logs/$M.time env PATH=/usr/bin:/bin LEAN_SYSROOT=$SYS LEAN_PATH=$OUT:$L/objs:$L/base_ref \
    timeout 300 $SYS/bin/lean -j1 -M7000 -DElab.async=false -R $SRC -o $OUT/$M.olean $SRC/$M.lean > $R/logs/$M.out 2> $R/logs/$M.err
  rc=$?
  printf '%s\t%s\t%s\t%s\n' "$M" "$s" "$rc" "$(tail -1 $R/logs/$M.time)" >> $R/manifest.tsv
  [ $rc -eq 0 ] || { echo "FAILED $M" > $R/DONE; date -u +%FT%TZ > $R/finished; exit 1; }
done < $R/order.txt
date -u +%FT%TZ > $R/finished
grep -h "depends on axioms" $R/logs/*.out | sed 's/.*depends on axioms: //' | sort | uniq -c > $R/axioms_summary.txt
grep -h "does not depend on any axioms" $R/logs/*.out | wc -l > $R/no_axioms_count.txt
grep -h "depends on axioms" $R/logs/AspisFailureBoundModel.out > $R/top_axioms.txt 2>/dev/null
grep -c "warning" $R/logs/*.out | grep -v ":0$" > $R/warnings.txt
grep -l "sorry" $R/logs/*.out > $R/sorry_mentions.txt 2>/dev/null
sha256sum $R/manifest.tsv > $R/manifest.tsv.sha256
echo "OK $(wc -l < $R/manifest.tsv) modules" > $R/DONE
