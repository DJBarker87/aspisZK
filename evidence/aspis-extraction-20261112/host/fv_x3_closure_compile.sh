#!/bin/bash
# X3 stage C: compile a module table in dependency order under the native toolchain, WITHOUT editing any file.
# A module with an in-table import that did not compile is skipped (named in the result). Per module: log, exit,
# wall, peak RSS, error count, first error. Sources are read in place; only objects are written, under <outdir>/out.
# Runs INSIDE one fv_slot.sh scope:
#   bash W/fv_slot.sh X3-C-<name> <timeout> bash W/x3/bin/fv_x3_closure_compile.sh <table.tsv> <outdir>
# Only imports that are rows of the table gate a module; other imports resolve from the object path.
# <table.tsv>: a table with a header holding the columns `module`, `path`, `closure_imports` (fv_x3_closure.py or
# fv_x3_kinds.py output), rows in dependency order. Writes <outdir>/result.tsv and <outdir>/PROGRESS.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
B=$W/x3/aeneas-src/backends/lean
# Overrides for the old-toolchain run: X3_TCD (toolchain dir) and X3_LPBASE (object path after <outdir>/out).
TCD=${X3_TCD:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2}
T=$1; O=$2
mkdir -p $O/out $O/log $O/ok
if [ -n "${X3_LPBASE:-}" ]; then LP=$O/out:$X3_LPBASE; else
  LP=$O/out:$B/.lake/build/lib/lean
  for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
fi
echo "TCD=$TCD" > $O/env.txt; echo "LEAN_PATH=$LP" >> $O/env.txt
# Resume: a module whose ok/<m> marker holds the same "sha256(source) imports" key as now is not recompiled;
# its row from the previous result is kept with "(reused)" appended. Earlier results move to result.prev.tsv.
[ -s $O/result.tsv ] && cat $O/result.tsv >> $O/result.prev.tsv
: > $O/result.tsv
python3 -I -c '
import sys
r=[l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
h=r[0]; i,p,c=h.index("module"),h.index("path"),h.index("closure_imports")
for x in r[1:]: print(x[i], x[p], x[c] or "-", sep="\t")
' $T > $O/plan.tsv
rm -rf $O/inplan; mkdir -p $O/inplan; cut -f1 $O/plan.tsv | while read -r m; do : > "$O/inplan/$m"; done
n=0
while IFS=$'\t' read -r m path imps; do
  n=$((n+1)); echo "$n $m" > $O/PROGRESS
  skip=""
  if [ "$imps" != "-" ]; then
    for i in ${imps//,/ }; do [ -f $O/inplan/$i ] || continue; [ -f $O/ok/$i ] || { skip=$i; break; }; done
  fi
  if [ -n "$skip" ]; then printf '%s\tskipped\t\t\t\timport not compiled: %s\n' "$m" "$skip" >> $O/result.tsv; continue; fi
  key="$(sha256sum "$path" | cut -c1-64) $imps"
  if [ -f $O/ok/$m ] && [ "$(cat $O/ok/$m)" = "$key" ] && [ -f $O/out/${m//.//}.olean ]; then
    prev=$(grep -P "^\Q$m\E\t0\t" $O/result.prev.tsv | tail -1)
    printf '%s\t(reused)\n' "$prev" >> $O/result.tsv; continue
  fi
  rm -f $O/ok/$m
  rel=${m//.//}; mkdir -p $O/out/$(dirname $rel)
  root=${path%/$rel.lean}
  s=$(date +%s.%N)
  /usr/bin/time -v -o $O/log/$m.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 900 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -R $root -o $O/out/$rel.olean -i $O/out/$rel.ilean $path > $O/log/$m.log 2>&1
  rc=$?; e=$(date +%s.%N)
  rss=$(grep "Maximum resident" $O/log/$m.time | awk '{print $NF}')
  nerr=$(grep -c ": error" $O/log/$m.log)
  first=$(grep -m1 ": error" $O/log/$m.log | tr '\t' ' ' | cut -c1-400)
  [ $rc -eq 0 ] && echo "$key" > $O/ok/$m
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$m" "$rc" "$(python3 -c "print(round($e-$s,2))")" "$rss" "$nerr" "$first" >> $O/result.tsv
done < $O/plan.tsv
echo "done $n" > $O/PROGRESS
