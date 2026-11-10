#!/bin/bash
# PCXF_shramt.sh: PCXF_SHRAMT_UPGRADED.json = definitions whose credit rests on the ShrAmt bridge (NPE_ check, overflow-checks-OFF only), from the compose2 tables.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6u/evidence/prov-p6u-20261110
python3 -I -B - <<'PY'
import sys, json
sys.path.insert(0, '.')
import PCXF_lib as L
mods = json.load(open(L.SCR + '/compose2_modules.json')); out = []
pcui = {tuple(x) for x in L.J('prov-p2i-20261110/PCUI_HAND_MODELS.json')['entries'][0]['credited_definitions_depending_on_it']}
for m, v in mods.items():
    for n, r in v['definitions'].items():
        if r.get('shramt_bridge') or (m, n) in pcui:
            out.append(dict(module=m, definition=n, status=r['status'], in_splitB_cone=r['in_splitB_cone'], via='NPE_ upgrade of the PCQH ShrAmt-conditional record' if r.get('shramt_bridge') else 'PCUI_ ShrAmt prelude (PRVEq_NJS_Extract_Funs_i2), OFF_EMISSION_WRAPPING_DECL'))
json.dump(out, open('PCXF_SHRAMT_UPGRADED.json', 'w'), indent=1); print(len(out), sum(1 for x in out if x['in_splitB_cone']))
PY
