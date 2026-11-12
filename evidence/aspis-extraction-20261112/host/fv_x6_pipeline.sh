#!/bin/bash
# X6: regenerate the carried source set of X3 revision 6 into W/x6 (X3 directories are read only).
# Steps 1-5 are fv_x3_pipeline4.sh with every output directory moved to W/x6:
#   1. sha256 of the aspis-lib6 copy (W/x6/aspis-lib6, a cp -a of W/x3/aspis-lib6); bases copied to its bases/
#   2. trim_imports.py --omit --map --stub on the L187 kind (c) modules that import a carrier or omitted module
#   3. drop_decls.py with W/x6/drop-decls.tsv (copy of W/x3/drop-decls4.tsv = drop-decls-r6.tsv)
#   4. chain: trim_imports.py on the 77 chain modules (copy of W/x3/chain-src-d012); only import lines may change
#   5. fv_x6_plan.py: carried set = import closure of the 73 model-chain modules and the bases (the four 33-row
#      side modules are not carried), full compile table in dependency order, gate
#   6. materialise: copy every carried source to W/x6/carried-src/<Module/Path>.lean (copies, no link), manifest
# Step 6 of X3 (hardlinking L187 objects) is not done: under 4.36.0-rc2 every carried module is compiled.
set -eu
W=/home/dombarker/project-offloads/future-version-20261111
X3=$W/x3; X=$W/x6; A=$X/aspis-lib6; C3=$X3/closure; C=$X/closure; T=$X/trimmed; CS=$X/chain-src; CT=$X/chain-trimmed
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
mkdir -p $C
cd $A; sha256sum $(find . -maxdepth 1 -type f ! -name SHA256SUMS.host | sort) > SHA256SUMS.host
mkdir -p bases; rm -f bases/*.lean; cp AspisLib_*.lean AspisHonestBudgetBase.lean bases/
MAP=""; while IFS== read -r k v; do [ -n "$k" ] && MAP="$MAP --map $k=$v"; done < $A/IMPORT_MAP.txt
DLIST=$C3/d-report.tsv
STUB=""; [ -f $A/STUB_MAP.txt ] && STUB="--stub $(sed -n 's/^STUB_MAP: *//p' $A/STUB_MAP.txt | head -1)"
OM=$X/omit.txt
python3 -I - $C3/closure-modules.tsv $OM $C/closure.tsv $C/trim-list.txt <<'PYEOF'
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
rm -rf $T; mkdir -p $T
python3 -I $A/trim_imports.py $L/src $T $DLIST --omit $OM $MAP $STUB $(cat $C/trim-list.txt) > $X/trim.log
python3 -I $A/drop_decls.py $L/src $T $X/drop-decls.tsv > $X/drop.log
rm -rf $CS $CT; mkdir -p $CS $CT
cp $X/chain-src-d012/*.lean $CS/
for m in $(tail -n +2 $DLIST | cut -f1) $(cat $OM); do
  r=${m//.//}; mkdir -p $CS/$(dirname $r); cp $L/src/$r.lean $CS/$r.lean
done
python3 -I $A/trim_imports.py $CS $CT $DLIST --omit $OM $MAP $STUB $(cat $X/bin/host-order-77.txt) > $X/chain-trim.log
: > $X/chain-diff.txt
for m in $(cat $X/bin/host-order-77.txt); do
  diff $X/chain-src-d012/$m.lean $CT/$m.lean > $X/.chd || true
  if [ -s $X/.chd ]; then
    echo "== $m" >> $X/chain-diff.txt; cat $X/.chd >> $X/chain-diff.txt
    if grep -E '^[<>] ' $X/.chd | grep -vqE '^[<>] import [A-Za-z0-9_.]+\s*$'; then echo "NON-IMPORT CHANGE in $m"; exit 9; fi
  fi
done
rm -f $X/.chd
python3 -I $X/bin/fv_x6_plan.py $C/closure.tsv $T $A/bases $CT $X/bin/host-order-model-73.txt \
  $C/plan-table.tsv $C/plan-gate.tsv
# 6
rm -rf $X/carried-src; mkdir -p $X/carried-src
python3 -I - $C/plan-table.tsv $X/carried-src $C/carried-table.tsv $X/MANIFEST.sha256 <<'PYEOF'
import hashlib, os, shutil, sys
tab, root, out, man = sys.argv[1:5]
rows = [l.rstrip("\n").split("\t") for l in open(tab)]
h = rows[0]; seen = {}
with open(out, "w") as f, open(man, "w") as g:
    f.write("\t".join(h + ["origin", "sha256"]) + "\n")
    for r in rows[1:]:
        d = dict(zip(h, r)); rel = d["module"].replace(".", "/") + ".lean"
        assert rel not in seen, rel; seen[rel] = 1
        dst = os.path.join(root, rel); os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(d["path"], dst)
        s = hashlib.sha256(open(dst, "rb").read()).hexdigest()
        f.write("\t".join([d[k] if k != "path" else dst for k in h] + [d["path"], s]) + "\n")
        g.write(f"{rel}\t{s}\n")
PYEOF
LC_ALL=C sort $X/MANIFEST.sha256 -o $X/MANIFEST.sha256
echo "modules $(wc -l < $X/MANIFEST.sha256) lines $(cat $(find $X/carried-src -name '*.lean') | wc -l) manifest_sha256 $(sha256sum $X/MANIFEST.sha256 | cut -c1-64)"
