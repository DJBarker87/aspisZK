#!/bin/bash
# PCXB_final.sh: PCXB_SUPERSEDED.json and the numbers used by PCXB_STATUS_LINE.md / PCXB_REPORT.md (printed).
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, collections, re
sys.path.insert(0, '.')
import PCXB_lib as L
P = json.load(open('PCXB_PROVENANCE.json')); S = P['summary']; A = json.load(open('PCXB_AUDIT.json')); R = json.load(open('PCXB_R22_SPLIT.json')); HM = json.load(open('PCXB_HAND_MODELS.json')); EX = json.load(open('PCXB_EXTERNALS_601.json'))
mods = json.load(open(L.SCR + '/compose2_modules.json')); pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
orows = set()
for m, v in mods.items():
    if v['rollup'] == 'OPEN':
        for r in pco[m]['rows']: orows.add(r)
paths = [l.strip() for l in open(L.SCR + '/all_lean_paths.txt')]
cred = {f['path'] for f in json.load(open('PCXB_CREDITED_FILES.json'))['files']}
allp = [p for p in paths if re.search(r'/PRVEq_[^/]*\.lean$', p) and not re.search(r'/(gen|probe\d?|failed_shapes|ingested)/|/PC[A-Z]{2,3}_L\d+|/sources/|prov-p6s|prov-p6c|bundle|diag', p)]
sup = sorted(p for p in allp if p not in cred)
json.dump(dict(schema='PCXB_SUPERSEDED/1', rule='PRVEq files in the evidence tree that are not the proving file of any credited (EQUALITY_PROVED / EQUALITY_DOMAIN / CONDITIONAL_ON_BINDING) PCQH_ALL_STATUS record: superseded by a later record, wrong basis, or proving an OPEN record. Excluded from the combined import. Scratch files with sorry (PRVC_N02_exp*, PCVB_L025/L030/L031 probe copies, PRVEq_probe1/probe3) are excluded a fortiori; no credited file contains sorry, native_decide or an axiom declaration (PCXB_CREDITED_FILES.json flags).', n=len(sup), files=sup), open('PCXB_SUPERSEDED.json', 'w'), indent=1)
sb = S['splitB_cone']
opens = collections.Counter()
for m, v in mods.items():
    for n, r in v['definitions'].items():
        if r['in_splitB_cone'] and r['status'] == 'OPEN': opens[r['open_class']] += 1
print(json.dumps(dict(sb=sb, rows=S['rows'], rows_relying_on_OPEN_module=len(orows), opens=dict(opens), r22=R['counts'], hm=HM['counts'], ext=EX['counts'], superseded=len(sup))))
open('PCXB_NUMBERS.json', 'w').write(json.dumps(dict(sb=sb, closed=S['CLOSED_roots_union'], rows=S['rows'], rows_relying_on_OPEN_module=len(orows), opens=dict(opens), r22=R['counts'], hm=HM['counts'], ext=EX['counts'], superseded=len(sup)), indent=1))
PY
