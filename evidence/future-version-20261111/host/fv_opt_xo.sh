#!/bin/bash
# Optimisation rounds: translator check of one source tree with the extraction probe's tools
# (EXTRACTION-PROBE.md section 4), second tool pair, roots, boundaries and features of XP-C12.
# Usage: fv_opt_xo.sh <tag> <tree>        tag: lower-case letters and digits (Lean namespace AspisXO<tag>)
# Steps: Charon (XO-C-<tag>), Aeneas without -abort-on-error so one pass lists every rejected function
# (XO-A-<tag>), the probe's header adaptation into $W/lean-src/AspisXO<tag>*.lean, four Lean compiles
# against the R1 (L187) objects by reference through fv_lean.sh (XO-L-<tag>-*), then the per-declaration
# error maps of Aeneas and Lean. The probe's tools are copied unchanged into extract-probe/xo/ except
# that XP_charon.py there takes its cargo target directory per source tree (target/second-verifier-<tree>).
# Time is expected in Charon's cold dependency build (a minute or two) and Aeneas (about a minute).
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/extract-probe/xo
TAG=$1; T=$2
D=$W/OPT_XO_$TAG.done; rm -f $D
cd $X
python3 - "$TAG" "$W/$T" > $X/spec-$TAG.json <<'PY'
import json, sys
s = json.load(open('/home/dombarker/project-offloads/future-version-20261111/extract-probe/XP-C12.json'))
s['run'] = 'XO-C-' + sys.argv[1]; s['src'] = sys.argv[2]
s['note'] = 'optimisation rounds: XP-C12 roots, boundaries and features on ' + sys.argv[2]
print(json.dumps(s, indent=1))
PY
bash $W/fv_slot.sh XO-C-$TAG 1800 python3 $X/XP_charon.py $X/spec-$TAG.json; echo "charon exit $?" >> $D
bash $W/fv_slot.sh XO-A-$TAG 1800 python3 $X/XP_aeneas.py XO-C-$TAG XO-A-$TAG second AspisXO$TAG noabort; echo "aeneas exit $? (noabort: nonzero when any function is rejected)" >> $D
python3 $X/XP_aeneas_summary.py XO-A-$TAG $X/aeneas-errors-$TAG.json > $X/aeneas-errors-$TAG.txt
python3 $X/XP_adapt.py $X/runs/XO-A-$TAG/raw/AspisXO$TAG AspisXO$TAG AspisXO$TAG $W/lean-src $X/XP_rules_newlib.json > $X/adapt-$TAG.json
for m in TypesExternal Types FunsExternal Funs; do
  bash $W/fv_lean.sh XO-L-$TAG-$m AspisXO$TAG$m > /dev/null; echo "lean $m exit $?" >> $D
done
python3 $X/XP_errmap.py $W/lean-src/AspisXO${TAG}Funs.lean $W/receipts/XO-L-$TAG-Funs/stdout.log $X/lean-errors-$TAG.json > $X/lean-errors-$TAG.txt
head -1 $X/lean-errors-$TAG.txt >> $D
echo DONE >> $D
