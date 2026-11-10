#!/bin/bash
# PCXD_notattempted.sh: PCXD_NOT_ATTEMPTED_23.json = the 23 FAILED records P2j did not attempt (PCUJ_SECOND_SHAPES.json), with their PCXD status and cone flag.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r/evidence/prov-p6r-20261110
python3 -I -B - <<'PY'
import json, collections, sys
sys.path.insert(0, '.')
import PCXD_lib as L
ss = json.load(open('../prov-p2j-20261110/PCUJ_SECOND_SHAPES.json'))['by_definition']
P = json.load(open('PCXD_PROVENANCE.json'))['modules']
st = json.load(open('../prov-p2j-20261110/PCUJ_ALL_STATUS.json'))['modules']
idx = {}
for m, dd in st.items():
    for n in dd: idx.setdefault(n, []).append(m)
out = []
for d, v in ss.items():
    if v['attempted']: continue
    ms = idx.get(d, [])
    rec = None
    for m in ms:
        pr = P.get(m, {}).get('definitions', {}).get(d)
        out.append(dict(definition=d, module=m, status_now=(pr['status'] if pr else st[m][d]['status']), in_splitB_cone=bool(pr and pr['in_splitB_cone']), open_reason_in_status=(st[m][d].get('open_reason') or '')[:160], why_not_attempted=v.get('reason'), proposed_shape=v.get('proposed_shape')))
json.dump(dict(schema='PCXD_NOT_ATTEMPTED_23/1', note='These 23 FAILED records were not attempted by P2j (PCUJ_SECOND_SHAPES.json). They are OPEN in PCXD_PROVENANCE.json; nothing here counts them as proved.', n_definitions=len(out), records=out), open('PCXD_NOT_ATTEMPTED_23.json', 'w'), indent=1)
print(len(out), collections.Counter(x['status_now'] for x in out), sum(1 for x in out if x['in_splitB_cone']))
for x in out: print(x['module'], '|', x['definition'][-60:], '|', x['status_now'], x['in_splitB_cone'], '|', (x['why_not_attempted'] or '')[:90])
PY
