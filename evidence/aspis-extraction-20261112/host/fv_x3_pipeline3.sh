#!/bin/bash
# X3 trimmed-copy pipeline, research 242907bd5b0 aspis-lib (README-ORDER.md). Text steps only (no Lean):
#  1. carrier list = 38 kind (d) modules + OMIT_MODULES.txt (16); closure table with the omitted modules as kind d
#  2. trim_imports.py --map (IMPORT_MAP.txt) on every non-omitted kind (c) module importing a carrier or an omitted
#     module, into W/x3/trimmed3
#  3. drop_decls.py over the same directory (reads the trimmed copy where one exists)
#  4. node table (bases + every kind (c) module downstream of a change) and the chain appended; import-graph check
# Usage: bash fv_x3_pipeline3.sh
set -eu
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x3; A=$X/aspis-lib3; C=$X/closure; T=$X/trimmed3
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/src
cd $A; sha256sum $(find . -maxdepth 1 -type f ! -name SHA256SUMS.host | sort) > SHA256SUMS.host
mkdir -p bases; cp AspisLib_*.lean AspisHonestBudgetBase.lean bases/
# 1
{ echo d_module; tail -n +2 $C/d-report.tsv | cut -f1; cat $A/OMIT_MODULES.txt; } > $C/carriers3.tsv
python3 -I - $C/closure-modules.tsv $A/OMIT_MODULES.txt $C/closure3.tsv $C/trim3-list.txt <<'EOF'
import sys
cl, om, out, tl = sys.argv[1:5]
omit = {l.strip() for l in open(om) if l.strip()}
rows = [l.rstrip("\n").split("\t") for l in open(cl)]
h = rows[0]; ki = h.index("kind")
kind = {r[0]: ("d" if r[0] in omit else r[ki]) for r in rows[1:]}
with open(out, "w") as f:
    f.write("\t".join(h) + "\n")
    for r in rows[1:]:
        r = list(r); r[ki] = kind[r[0]]; f.write("\t".join(r) + "\n")
ci = h.index("closure_imports")
with open(tl, "w") as f:
    for r in rows[1:]:
        if kind[r[0]] == "c" and any(kind.get(i) == "d" for i in r[ci].split(",") if i):
            f.write(r[0] + "\n")
EOF
MAP=""; while IFS== read -r k v; do [ -n "$k" ] && MAP="$MAP --map $k=$v"; done < $A/IMPORT_MAP.txt
rm -rf $T; mkdir -p $T
# 2
python3 -I $A/trim_imports.py $L $T $C/carriers3.tsv $MAP $(cat $C/trim3-list.txt) > $X/trim3.log
# 3
python3 -I $A/drop_decls.py $L $T $A/DROP_DECLS.tsv > $X/drop3.log
# 4
python3 -I $X/bin/fv_x3_mapplan.py $C/closure3.tsv $T $A/bases $C/map3-table.tsv $C/map3-check.tsv
python3 -I $X/bin/fv_x3_chainplan.py $C/closure3.tsv $C/map3-table.tsv $X/chain-src-d012 $X/bin/host-order-77.txt \
  $C/chain3-table.tsv $C/chain3-check.tsv
echo "trimmed $(wc -l < $C/trim3-list.txt); drop log:"; cat $X/drop3.log
