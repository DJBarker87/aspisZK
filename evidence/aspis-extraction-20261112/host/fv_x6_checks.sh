#!/bin/bash
# X6 statement checks under Lean 4.36.0-rc2 (fv_x3_checks4.sh with the new toolchain and the X6 object set).
# Runs INSIDE one fv_slot.sh scope:  bash W/fv_slot.sh X6-checks-<n> <timeout> bash W/x6/bin/fv_x6_checks.sh <checkdir>
# <checkdir> holds copies of X3's check files (X5Statements.lean, AspisChainUsesD.lean, ImportGraph.lean,
# closure_d.py, statements-before.out) and the X6 file X6Extra.lean. LEAN_PATH: W/x6/objs, then the stage A library
# objects. No L187 directory and no W/x3 object directory of carried modules is on it.
#  a, b: X5Statements.out (both #check, both #print axioms, both pp.all #check) against statements-before.out (cmp)
#  d:    import closure of AspisFailureBoundModel as loaded (ImportGraph) against the kind (d) list and the omit list;
#        and a scan of every LEAN_PATH directory for an object of a kind (d) or omitted module
set -u
W=/home/dombarker/project-offloads/future-version-20261111; Y=$W/x6; B=$W/x3/aeneas-src/backends/lean
K=$1
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
LP=$Y/objs:$B/.lake/build/lib/lean; for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
cd $K
echo "LEAN_PATH=$LP" > env.txt; $TCD/bin/lean --version >> env.txt
: > exits.txt
for f in X5Statements AspisChainUsesD ImportGraph X6Extra; do
  [ -f $f.lean ] || continue
  /usr/bin/time -v -o $f.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 1800 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false $f.lean > $f.out 2>&1
  echo "$f exit $?" >> exits.txt
done
cmp X5Statements.out statements-before.out > check-b.txt 2>&1 && echo "IDENTICAL" >> check-b.txt
sha256sum X5Statements.out statements-before.out >> check-b.txt
grep "depends on axioms" X5Statements.out > check-a.txt
tail -n +2 $W/x3/closure/d-report.tsv | cut -f1 > dlist.txt
cat dlist.txt $Y/omit.txt > dlist-plus-omit.txt
python3 -I closure_d.py import_graph.tsv dlist.txt $Y/bin/host-order-77.txt > check-d.txt 2>&1
python3 -I closure_d.py import_graph.tsv dlist-plus-omit.txt $Y/bin/host-order-77.txt > check-d-omit.txt 2>&1
# LEAN_PATH scan
: > check-d-leanpath.txt; n=0
for d in ${LP//:/ }; do
  while read -r m; do
    [ -n "$m" ] || continue
    if [ -e "$d/${m//.//}.olean" ]; then echo "FOUND $d ${m}" >> check-d-leanpath.txt; n=$((n+1)); fi
  done < dlist-plus-omit.txt
done
echo "lean_path_dirs $(echo ${LP//:/ } | wc -w) kind_d_or_omitted_objects_found $n" >> check-d-leanpath.txt
echo done > DONE
