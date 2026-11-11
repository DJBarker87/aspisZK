#!/bin/bash
# Translatability pass, core and decoders (worker 3): adapt one Aeneas emission of tp3-xp/runs/<run>
# into four flat Lean modules named <prefix>{TypesExternal,Types,FunsExternal,Funs} under lean-src and
# compile them one at a time through fv_lean.sh (6G/8G, no swap, Lean 4.32.0 against the L187 objects),
# with the extraction probe's adaptation rules (header changes and the AspisXPNewLib shim only).
# Usage: fv_tp3_lean.sh <aeneas-run> <namespace> <prefix> <attempt-prefix> [norules]
# norules: header changes only (first-pair emissions need no library shim).
# Time is expected in the Lean compiles (seconds to a minute per module).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
RUN=$1; NS=$2; PRE=$3; AP=$4; RULES=tp3-xp/XP_rules_newlib.json; [ "${5:-}" = norules ] && RULES=
cd $W
python3 tp3-xp/XP_adapt.py tp3-xp/runs/$RUN/raw/$NS $NS $PRE lean-src $RULES > tp3-xp/runs/$RUN/adapt.json || exit 1
for m in TypesExternal Types FunsExternal Funs; do
  test -f lean-src/$PRE$m.lean || continue
  bash fv_lean.sh $AP-$m $PRE$m > tp3-xp/runs/$RUN/lean-$m.out 2>&1
  echo "$PRE$m exit $(cat receipts/$AP-$m/exit)" | tee -a tp3-xp/runs/$RUN/lean.summary
done
