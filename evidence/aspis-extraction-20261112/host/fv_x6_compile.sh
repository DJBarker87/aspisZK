#!/bin/bash
# X6: compile the carried set under Lean 4.36.0-rc2 in dependency order, one module at a time, no file edited.
# fv_x3_closure_compile.sh with these changes:
#  - sources: W/x6/ported-src (the carried tree with port patches applied); objects: W/x6/objs;
#  - LEAN_PATH: W/x6/objs, then the stage A library objects of W/x3/aeneas-src by reference (Aeneas, Mathlib and the
#    other packages of its lake manifest). No L187 directory and no W/x3 object directory of carried modules.
#  - resume key = sha256 over (source sha256, in-table imports, keys of the in-table imports), so a module is
#    recompiled whenever a dependency changed;
#  - reuse of X3 pass 2 (W/x3/pass2, read only): a module whose pass-2 source has the same sha256, that compiled
#    there (ok marker), and all of whose in-table imports were reused the same way, has its objects COPIED (cp, not
#    a link) into W/x6/objs instead of being recompiled; its row says "reused-x3-pass2".
# Runs INSIDE one fv_slot.sh scope:  bash W/fv_slot.sh X6-<name> <timeout> bash W/x6/bin/fv_x6_compile.sh <table> <outdir>
# <table>: closure/carried-table.tsv (module, kind, path, lines, closure_imports, ...). Results: <outdir>/result.tsv
# (module, kind, exit|skipped|reused-x3-pass2, wall s, peak RSS kB, error count, first error).
# A failed module is keyed in <outdir>/fail and not rerun until its key changes.
# Optional env X6_STOP_AFTER=<module>: stop after that module.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
Y=$W/x6; P2=$W/x3/pass2; B=$W/x3/aeneas-src/backends/lean
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
T=$1; O=$2; SRC=$Y/ported-src; OBJ=$Y/objs
mkdir -p $OBJ $O/log $O/ok $O/key $O/fail
LP=$OBJ:$B/.lake/build/lib/lean
for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
echo "TCD=$TCD" > $O/env.txt; echo "LEAN_PATH=$LP" >> $O/env.txt; $TCD/bin/lean --version >> $O/env.txt
[ -s $O/result.tsv ] && cat $O/result.tsv >> $O/result.prev.tsv
: > $O/result.tsv
python3 -I -c '
import sys
r=[l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
h=r[0]; i,k,c=h.index("module"),h.index("kind"),h.index("closure_imports")
for x in r[1:]: print(x[i], x[k], x[c] or "-", sep="\t")
' $T > $O/plan.tsv
# pass-2 source sha256 per module
python3 -I -c '
import hashlib,sys
for l in open(sys.argv[1]):
    m,p=l.split("\t")[:2]
    print(m, hashlib.sha256(open(p,"rb").read()).hexdigest(), sep="\t")
' $P2/plan.tsv > $O/pass2-src.sha
rm -rf $O/inplan $O/reusable; mkdir -p $O/inplan $O/reusable
cut -f1 $O/plan.tsv | while read -r m; do : > "$O/inplan/$m"; done
n=0
while IFS=$'\t' read -r m kind imps; do
  n=$((n+1)); echo "$n $m" > $O/PROGRESS
  rel=${m//.//}; path=$SRC/$rel.lean
  skip=""; dk=""; allre=1
  if [ "$imps" != "-" ]; then
    for i in ${imps//,/ }; do
      [ -f $O/inplan/$i ] || continue
      [ -f $O/ok/$i ] || { skip=$i; break; }
      dk="$dk $(cat $O/key/$i)"; [ -f $O/reusable/$i ] || allre=0
    done
  fi
  if [ -n "$skip" ]; then printf '%s\t%s\tskipped\t\t\t\timport not compiled: %s\n' "$m" "$kind" "$skip" >> $O/result.tsv; continue; fi
  ssha=$(sha256sum "$path" | cut -c1-64)
  key=$(printf '%s %s%s' "$ssha" "$imps" "$dk" | sha256sum | cut -c1-64)
  echo "$key" > $O/key/$m
  if [ -f $O/ok/$m ] && [ "$(cat $O/ok/$m)" = "$key" ] && [ -f $OBJ/$rel.olean ]; then
    prev=$(grep -P "^\Q$m\E\t" $O/result.prev.tsv | grep -vP "\tskipped\t" | tail -1)
    [ -f $O/reusable.prev/$m ] && : > $O/reusable/$m
    printf '%s\t(resumed)\n' "$prev" >> $O/result.tsv; continue
  fi
  if [ -f $O/fail/$m ] && [ "$(cat $O/fail/$m)" = "$key" ]; then
    # an unchanged failure is never rerun (AGENTS.md: a failed or killed job is changed before it runs again)
    prev=$(grep -P "^\Q$m\E\t" $O/result.prev.tsv | grep -vP "\tskipped\t" | tail -1)
    printf '%s\t(failed earlier, unchanged, not rerun)\n' "$prev" >> $O/result.tsv; continue
  fi
  rm -f $O/ok/$m $O/fail/$m
  mkdir -p $OBJ/$(dirname $rel)
  p2sha=$(grep -P "^\Q$m\E\t" $O/pass2-src.sha | cut -f2)
  if [ $allre -eq 1 ] && [ "$p2sha" = "$ssha" ] && [ -f $P2/ok/$m ] && [ -f $P2/out/$rel.olean ]; then
    cp $P2/out/$rel.olean $P2/out/$rel.ilean $OBJ/$(dirname $rel)/
    for x in olean.private olean.server ir ir.sig; do [ -f $P2/out/$rel.$x ] && cp $P2/out/$rel.$x $OBJ/$(dirname $rel)/; done
    echo "$key" > $O/ok/$m; : > $O/reusable/$m
    printf '%s\t%s\treused-x3-pass2\t\t\t0\t\n' "$m" "$kind" >> $O/result.tsv; continue
  fi
  s=$(date +%s.%N)
  /usr/bin/time -v -o $O/log/$m.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 900 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -R $SRC -o $OBJ/$rel.olean -i $OBJ/$rel.ilean $path > $O/log/$m.log 2>&1
  rc=$?; e=$(date +%s.%N)
  rss=$(grep "Maximum resident" $O/log/$m.time | awk '{print $NF}')
  nerr=$(grep -c ": error" $O/log/$m.log)
  first=$(grep -m1 ": error" $O/log/$m.log | tr '\t' ' ' | cut -c1-400)
  if [ $rc -eq 0 ]; then echo "$key" > $O/ok/$m; else echo "$key" > $O/fail/$m; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$m" "$kind" "$rc" "$(python3 -c "print(round($e-$s,2))")" "$rss" "$nerr" "$first" >> $O/result.tsv
  [ "${X6_STOP_AFTER:-}" = "$m" ] && break
done < $O/plan.tsv
rm -rf $O/reusable.prev; cp -a $O/reusable $O/reusable.prev
echo "done $n" > $O/PROGRESS
