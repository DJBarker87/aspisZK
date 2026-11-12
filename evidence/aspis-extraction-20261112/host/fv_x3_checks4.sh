#!/bin/bash
# X3 step 3 checks a-e (repoint/README.md "Checks and expected outputs"), Lean 4.32.0, same LEAN_PATH as the build
# (own objects, the hardlinked carried L187 objects, L187 base_ref; never L187 objs). Runs INSIDE one fv_slot scope.
# Usage: fv_x3_checks4.sh <objdir> <checkdir>    (checkdir holds the check .lean files and tools, copied unchanged)
set -u
W=/home/dombarker/project-offloads/future-version-20261111; X=$W/x3
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
O=$1; K=$2
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0
LP=$O/out:$X/l187-carried4:$L/base_ref
cd $K
for f in X5Statements AspisChainUsesD ImportGraph; do
  /usr/bin/time -v -o $f.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 1800 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false $f.lean > $f.out 2>&1
  echo "$f exit $?" >> exits.txt
done
# b: byte identity with the recorded before printout
cmp X5Statements.out statements-before.out > check-b.txt 2>&1 && echo "IDENTICAL" >> check-b.txt
sha256sum X5Statements.out statements-before.out >> check-b.txt
# d and e: kind (d) modules in the closure of AspisFailureBoundModel, and the 33-row modules
tail -n +2 $X/closure/d-report.tsv | cut -f1 > dlist.txt
cat dlist.txt $X/aspis-lib4/OMIT_MODULES.txt > dlist-plus-omit.txt
python3 -I closure_d.py import_graph.tsv dlist.txt $X/bin/host-order-77.txt > check-d.txt 2>&1
python3 -I closure_d.py import_graph.tsv dlist-plus-omit.txt $X/bin/host-order-77.txt > check-d-omit.txt 2>&1
echo done > DONE
