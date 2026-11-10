#!/bin/bash
# PCXE_delta.sh: PCXE_DELTA.json = status transitions PCXB_ -> PCXE_ for the deployed_splitB cone definitions and for the 599-row view.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t/evidence
python3 -I -B - <<'PY'
import json, collections
a = json.load(open('prov-p6r-20261110/PCXD_PROVENANCE.json')); b = json.load(open('prov-p6t-20261110/PCXE_PROVENANCE.json'))
tr = collections.Counter(); why = collections.Counter(); ex = collections.defaultdict(list)
sbo = a['summary']['splitB_cone']; sbn = b['summary']['splitB_cone']
for m, v in b['modules'].items():
    if not v['in_splitB_cone']: continue
    for n, r in v['definitions'].items():
        if not r['in_splitB_cone']: continue
        old = a['modules'].get(m, {}).get('definitions', {}).get(n)
        os_ = old['status'] if old else 'ABSENT'
        if os_ != r['status']:
            k = (os_, r['status']); tr[k] += 1
            reason = r.get('basis_class') or ('PCXE overlay' if r.get('decided_by', '').startswith('P3b') else r.get('decided_by'))
            why[(os_, r['status'], str(reason))] += 1
            if len(ex[str(k)]) < 3: ex[str(k)].append(f'{m} :: {n}')
rollold = collections.Counter(); 
rows_old = a['summary']['rows']; rows_new = b['summary']['rows']
out = dict(schema='PCXE_DELTA/1', splitB_before=sbo, splitB_after=sbn, transitions={f'{k[0]} -> {k[1]}': v for k, v in sorted(tr.items())},
           transitions_by_reason=[dict(frm=k[0], to=k[1], reason=k[2], n=v) for k, v in sorted(why.items(), key=lambda x: -x[1])], examples=ex, rows_before=rows_old, rows_after=rows_new)
json.dump(out, open('prov-p6t-20261110/PCXE_DELTA.json', 'w'), indent=1)
print(json.dumps(out['transitions'], indent=0)); [print(x) for x in out['transitions_by_reason']]
print(sbo['module_rollups'], sbn['module_rollups'], sbo['definitions'], sbn['definitions'], rows_old, rows_new, sbo['open_wrong_basis_definitions'], sbn['open_wrong_basis_definitions'])
PY
