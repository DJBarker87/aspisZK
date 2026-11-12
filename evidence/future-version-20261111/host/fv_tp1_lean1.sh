#!/bin/bash
# Aspis translatability pass: Lean elaboration of an EXISTING Aeneas emission, in ONE fv_slot.sh scope (8 GiB cap).
# Usage: fv_tp1_lean1.sh <tag> <aeneas-run> <namespace> <flat-prefix> [<aeneas-run> <namespace> <flat-prefix>]...
#   per emission: TP_adapt.py with TP_rules_release.json (header change, listed naming rules, the shim AspisTPNewLib),
#   the four flat modules compiled one at a time against the R1 (L187) library (fv_lean_one.sh), each Lean error
#   assigned to the declaration it falls in (TP_errmap.py -> tp1/summaries/lean-<flat-prefix>.json).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
TAG=$1; shift
bash fv_slot.sh TP-L$TAG 3000 bash -c '
W='$W'; cd $W/tp1; ST=$W/tp1/lean1-'$TAG'.steps; : > $ST; mkdir -p flat summaries
while [ $# -ge 3 ]; do
  A=$1; NS=$2; PRE=$3; shift 3
  python3 TP_adapt.py runs/$A/raw/$NS $NS $PRE flat/$PRE TP_rules_release.json > summaries/adapt-$PRE.json || { echo "$PRE adapt failed" >> $ST; continue; }
  cp flat/$PRE/*.lean $W/lean-src/
  for M in TypesExternal Types FunsExternal Funs; do
    test -f $W/lean-src/$PRE$M.lean || { echo "lean $PRE$M absent" >> $ST; continue; }
    t0=$(date +%s); bash $W/fv_lean_one.sh $PRE$M > summaries/lean-$PRE$M.log 2>&1; rc=$?
    echo "lean-$PRE$M exit $rc; wall $(( $(date +%s) - t0 )) s; errors $(grep -c ": error" summaries/lean-$PRE$M.log)" >> $ST
  done
  python3 TP_errmap.py $W/lean-src/${PRE}Funs.lean summaries/lean-${PRE}Funs.log summaries/lean-$PRE.json > summaries/lean-$PRE.txt 2>&1
  head -1 summaries/lean-$PRE.txt >> $ST
done
echo DONE >> $ST' _ "$@" > $W/tp1/lean1-$TAG.log 2>&1
echo "scope exit $?"; cat $W/tp1/lean1-$TAG.steps 2>/dev/null | cut -c1-200
