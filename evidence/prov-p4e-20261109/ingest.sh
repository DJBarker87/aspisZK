# usage: bash ingest.sh MODULE RUN_LEAN EMIT_RUN NS TAG
cd "$(dirname "$0")"
M=$1; L=$2; RUN=$3; NS=$4; TAG=$5; F=$(echo $M | tr . _)
xz -dc $L/stdout.log.xz > $L.lean.log
python3 PCWE_gen_equalities.py --module $M --fresh-dir ${RUN}_emitted/raw/$NS --fresh-ns $NS --gate-source gatesrc/${TAG}_Funs.lean --gate-types-source gatesrc/${TAG}_Types.lean --partition ../prov-p0-20261109/PCO_PARTITION.json --out PRVEq_${F}.lean --report PRVEq_${F}.report.json --state PRVEq_${F}.state1.json --state-out PRVEq_${F}.state2.json --lean-log $L.lean.log | tail -1
python3 -c "import json;d=json.load(open('PRVEq_${F}.report.json'));print(d['counts'])"
