#!/bin/bash
# X3 trimmed-copy pipeline, revision 4 (research 0399fd132ef aspis-lib, README-ORDER.md). Text and link steps only.
#  1. install + sha256 of every aspis-lib file (W/x3/aspis-lib4); bases copied to aspis-lib4/bases
#  2. trim_imports.py --omit --map on the L187 kind (c) modules that import a carrier or omitted module -> trimmed4
#  3. drop_decls.py with W/x3/drop-decls4.tsv (the record's DROP_DECLS.tsv plus X3's additions)
#  4. chain: copy the 77 chain files and the L187 sources of the 54 carrier/omitted modules into chain4-src (copies),
#     trim_imports.py on all 77 chain modules -> chain4-trimmed; diff: only import lines may change
#  5. fv_x3_plan4.py: compile table, link list, gate
#  6. hardlink (cp -l, inside W/x3, no symlink) the L187 objects of the unchanged carried kind (c) modules into
#     W/x3/l187-carried4; the L187 objs directory is not put on LEAN_PATH
set -eu
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x3; A=${X3_LIB:-$X/aspis-lib4}; C=$X/closure; T=$X/trimmed4; CS=$X/chain4-src; CT=$X/chain4-trimmed
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
cd $A; sha256sum $(find . -maxdepth 1 -type f ! -name SHA256SUMS.host | sort) > SHA256SUMS.host
mkdir -p bases; rm -f bases/*.lean; cp AspisLib_*.lean AspisHonestBudgetBase.lean bases/
MAP=""; while IFS== read -r k v; do [ -n "$k" ] && MAP="$MAP --map $k=$v"; done < $A/IMPORT_MAP.txt
DLIST=$C/d-report.tsv
# working omit list: the record's OMIT_MODULES.txt plus X3 cascade additions (W/x3/omit4.txt, created if absent)
OM=$X/omit4.txt; [ -f $OM ] || cp $A/OMIT_MODULES.txt $OM
# closure table with omitted modules as kind d, and the trim list (kind (c) modules importing a carrier or omitted)
python3 -I - $C/closure-modules.tsv $OM $C/closure4.tsv $C/trim4-list.txt <<'PYEOF'
import sys
cl, om, out, tl = sys.argv[1:5]
omit = {l.strip() for l in open(om) if l.strip()}
rows = [l.rstrip("\n").split("\t") for l in open(cl)]
h = rows[0]; ki = h.index("kind"); ci = h.index("closure_imports")
kind = {r[0]: ("d" if r[0] in omit else r[ki]) for r in rows[1:]}
with open(out, "w") as f:
    f.write("\t".join(h) + "\n")
    for r in rows[1:]:
        r = list(r); r[ki] = kind[r[0]]; f.write("\t".join(r) + "\n")
with open(tl, "w") as f:
    for r in rows[1:]:
        if kind[r[0]] == "c" and any(kind.get(i) == "d" for i in r[ci].split(",") if i):
            f.write(r[0] + "\n")
PYEOF
# 2
rm -rf $T; mkdir -p $T
python3 -I $A/trim_imports.py $L/src $T $DLIST --omit $OM $MAP $(cat $C/trim4-list.txt) > $X/trim4.log
# 3
python3 -I $A/drop_decls.py $L/src $T $X/drop-decls4.tsv > $X/drop4.log
# 4
rm -rf $CS $CT; mkdir -p $CS $CT
cp $X/chain-src-d012/*.lean $CS/
for m in $(tail -n +2 $DLIST | cut -f1) $(cat $OM); do
  r=${m//.//}; mkdir -p $CS/$(dirname $r); cp $L/src/$r.lean $CS/$r.lean
done
python3 -I $A/trim_imports.py $CS $CT $DLIST --omit $OM $MAP $(cat $X/bin/host-order-77.txt) > $X/chain4-trim.log
: > $X/chain4-diff.txt
for m in $(cat $X/bin/host-order-77.txt); do
  diff $X/chain-src-d012/$m.lean $CT/$m.lean > /tmp/x3d.$$ || true
  if [ -s /tmp/x3d.$$ ]; then
    echo "== $m" >> $X/chain4-diff.txt; cat /tmp/x3d.$$ >> $X/chain4-diff.txt
    # every changed line must be an import line
    if grep -E '^[<>] ' /tmp/x3d.$$ | grep -vqE '^[<>] import [A-Za-z0-9_.]+\s*$'; then echo "NON-IMPORT CHANGE in $m"; exit 9; fi
  fi
done
rm -f /tmp/x3d.$$
# 5
python3 -I $X/bin/fv_x3_plan4.py $C/closure4.tsv $T $A/bases $CT $X/bin/host-order-77.txt \
  $C/plan4-table.tsv $C/plan4-link.txt $C/plan4-gate.tsv
# 6
rm -rf $X/l187-carried4; mkdir -p $X/l187-carried4; n=0
while read -r m; do
  [ -n "$m" ] || continue; r=${m//.//}; mkdir -p $X/l187-carried4/$(dirname $r)
  for f in $L/objs/$r.olean $L/objs/$r.ilean $L/objs/$r.olean.private $L/objs/$r.olean.server; do
    [ -f $f ] && { cp -l $f $X/l187-carried4/${f#$L/objs/}; n=$((n+1)); }
  done
  [ -f $L/objs/$r.olean ] || echo "MISSING OBJECT $m"
done < $C/plan4-link.txt
echo "hardlinked $n files"; find $X/l187-carried4 -type l | wc -l
