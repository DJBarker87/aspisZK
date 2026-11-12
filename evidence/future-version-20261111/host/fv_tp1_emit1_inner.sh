#!/bin/bash
# Runs INSIDE one fv_slot.sh scope (started by fv_tp1_emit1.sh). See that file.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W/tp1 || exit 1
TAG=$1; CV=$2; CP=$3
ST=$W/tp1/emit1-$TAG.steps; : > $ST; mkdir -p summaries flat
step() { local name=$1; shift; local t0=$(date +%s); "$@"; local rc=$?; echo "$name exit $rc; wall $(( $(date +%s) - t0 )) s" >> $ST; return $rc; }
one() { # scope letter, charon spec, namespace, crate prefix for the scan
  local X=$1 C=$2 NS=$3 CRATE=$4 A=TP-A$TAG$1 PRE=AspisTP1$TAG$1
  step charon-$X python3 TP_charon.py $C.json > summaries/charon-$C.txt 2>&1 || { tail -5 runs/$C/charon.log | cut -c1-300 >> $ST; return 1; }
  step aeneas-$X-noabort python3 TP_aeneas.py $C $A second $NS noabort > summaries/aeneas-$A.txt 2>&1
  python3 TP_aeneas_summary.py $A summaries/$A.json > summaries/$A.txt 2>&1
  local nerr=$(grep -c '^\[Error\]' runs/$A/aeneas.log)
  echo "aeneas-$X rejections (noabort run): $nerr" >> $ST
  local RAW=runs/$A/raw/$NS
  if [ "$nerr" = 0 ]; then
    step aeneas-$X-release python3 TP_aeneas.py $C ${A}R second $NS > summaries/aeneas-${A}R.txt 2>&1 && RAW=runs/${A}R/raw/$NS
    echo "release-style emission (with -abort-on-error): $(cat runs/${A}R/aeneas_result.json 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); print("exit", d["exit"], "files", len(d["outputs"]))' 2>/dev/null)" >> $ST
  fi
  echo "emission used for Lean and the scan: $RAW" >> $ST
  step scan-$X python3 TP_llbc_scan.py runs/$C $RAW summaries/scan-$C.json $CRATE > summaries/scan-$C.txt 2>&1
  tail -4 summaries/scan-$C.txt | cut -c1-300 >> $ST
  python3 TP_adapt.py $RAW $NS $PRE flat/$PRE TP_rules_release.json > summaries/adapt-$PRE.json || return 1
  cp flat/$PRE/*.lean $W/lean-src/ || return 1
  for M in TypesExternal Types FunsExternal Funs; do
    test -f $W/lean-src/$PRE$M.lean || { echo "lean $PRE$M absent" >> $ST; continue; }
    step lean-$PRE$M bash $W/fv_lean_one.sh $PRE$M > summaries/lean-$PRE$M.log 2>&1
    echo "   errors in $PRE$M: $(grep -c ': error' summaries/lean-$PRE$M.log)" >> $ST
  done
  python3 TP_errmap.py $W/lean-src/${PRE}Funs.lean summaries/lean-${PRE}Funs.log summaries/lean-$PRE.json > summaries/lean-$PRE.txt 2>&1
  head -1 summaries/lean-$PRE.txt >> $ST
}
# the shim of copied library definitions is compiled first (its source travels with the tools in tp1/)
if [ -f AspisTPNewLib.lean ]; then
  cmp -s AspisTPNewLib.lean $W/lean-src/AspisTPNewLib.lean || cp AspisTPNewLib.lean $W/lean-src/AspisTPNewLib.lean
  step lean-shim bash $W/fv_lean_one.sh AspisTPNewLib > summaries/lean-AspisTPNewLib-$TAG.log 2>&1
  echo "   shim source sha256 $(sha256sum $W/lean-src/AspisTPNewLib.lean | cut -c1-64); errors: $(grep -c ': error' summaries/lean-AspisTPNewLib-$TAG.log)" >> $ST
fi
one v $CV AspisTPv aspis_r1_cost_probe
one p $CP AspisTPp aspis_r1_cost_probe_program
echo DONE >> $ST
