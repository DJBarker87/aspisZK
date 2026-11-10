#!/bin/bash
# usage: bash PCQI_gen1.sh MODULE TAG FRESHDIR FRESHNS ONLYJSON|- [extra generator args...]
# fetches the gate (PRV_PARTITION first candidate) into inputs/, runs PCQI_gen_equalities.py, prints a short summary. Funs modules use the module's own text as types source unless GATETYPES env is set.
cd "$(dirname "$0")"
M=$1;T=$2;FD=$3;FNS=$4;ON=$5;shift 5
SAFE=${M//./_}
[ -f inputs/gate_$SAFE.lean ] || bash PCQI_gate.sh $M >/dev/null
GT=${GATETYPES:-inputs/gate_$SAFE.lean}
KIND=""; case $M in *Types) ;; *) ;; esac
ARGS=(--module $M --tag $T --fresh-dir $FD --fresh-ns $FNS --gate-source inputs/gate_$SAFE.lean --gate-types-source $GT --out PRVEq_${SAFE}$T.lean --report gen/${SAFE}$T.report.json --state-out gen/${SAFE}$T.state.json --prune-fresh)
[ "$ON" != "-" ] && ARGS+=(--only $ON)
python3 -B PCQI_gen_equalities.py "${ARGS[@]}" "$@" 2>&1 | tail -2 | cut -c1-300
python3 - <<PY
import json
d=json.load(open('gen/${SAFE}$T.report.json'))
print('${SAFE}$T','common',d['counts']['common_declarations'],'types_differs',d['types_identity']['differs'],'ext',d.get('external_funs'),d.get('external_types'))
PY
grep -c "^theorem PRVEq\|^def PRVEq" PRVEq_${SAFE}$T.lean
