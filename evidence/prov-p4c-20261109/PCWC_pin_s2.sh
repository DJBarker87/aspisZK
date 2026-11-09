#!/bin/bash
# PCWC_pin_s2.sh MODULE RUN NS TAG : regenerate PRVEq_<M> with every theorem pinned to stage S2 (delta both sides, rfl),
# using a synthetic marker log (shape change after the PCWC_L005/L007 timeouts of the first-chain probe).
set -e
cd "$(dirname "$0")"
M=$1; RUN=$2; NS=$3; TAG=$4; F=$(echo $M | tr . _)
python3 - "$M" "$F" <<'PY'
import json,sys
M,F=sys.argv[1:3]
s=json.load(open(f'PRVEq_{F}.state1.json'))
open(f'pin_s2_{F}.log','w').write(''.join(f'PRV-S2 PRVEq.{M}.{n}\n' for n in s['defs']))
PY
python3 PCWC_gen_equalities.py --module $M --fresh-dir ${RUN}_emitted/raw/$NS --fresh-ns $NS --gate-source gatesrc/${TAG}_Funs.lean --gate-types-source gatesrc/${TAG}_Types.lean --partition ../prov-p0-20261109/PCO_PARTITION.json --out PRVEq_${F}.lean --report PRVEq_${F}.report.json --state PRVEq_${F}.state1.json --state-out PRVEq_${F}.state2.json --lean-log pin_s2_${F}.log | tail -1
