#!/bin/bash
# Shape change after PCXA_L006 (bundle A6 exit 1: from_residual theorem of prov-p4a eq/PRVEq_S8OwnedP6_Funs.lean unsolved in the bundle context):
# A11 = that file alone, A12 = A6 without it. L006 is not rerun unchanged.
set -e
cd /Users/dominic/ZK/.worktrees/pc-prov-p6s/evidence
python3 -I - <<'PY'
import json
b = json.load(open('prov-p6s-20261109/PCXA_BUNDLES.json'))
audit = '\nsection PRVAudit\n' + open('prov-p6s-20261109/PRVEq_bundle_A1.lean').read().split('\nsection PRVAudit\n', 1)[1]
a6 = [x for x in b['bundles'] if x['bundle'] == 'PRVEq_bundle_A6'][0]['files']
s8 = 'prov-p4a-20261109/eq/PRVEq_S8OwnedP6_Funs.lean'
assert s8 in a6
def mk(nm, fl):
    imports = []; body = []
    for j, f in enumerate(fl):
        keep = []
        for l in open(f).read().split('\n'):
            if l.startswith('import '):
                if l not in imports: imports.append(l)
            else: keep.append(l)
        nc = any(l.strip() == 'noncomputable section' for l in keep)
        body += [f'section PRVBundle_{j}', '\n'.join(keep)] + (['end'] if nc else []) + [f'end PRVBundle_{j}']
    imps = [l for l in imports if l == 'import Aeneas'] + [l for l in imports if l != 'import Aeneas']
    open(f'prov-p6s-20261109/PRVEq_bundle_{nm}.lean', 'w').write('\n'.join([f'-- PCXA audit bundle {nm}: exact concatenation of ' + ', '.join(f.split('/')[-1] for f in fl)] + imps + ['']) + '\n'.join(body) + '\n' + audit)
mk('A11', [s8]); mk('A12', [f for f in a6 if f != s8])
b['bundles'] += [dict(bundle='PRVEq_bundle_A11', files=[s8]), dict(bundle='PRVEq_bundle_A12', files=[f for f in a6 if f != s8], replaces='PRVEq_bundle_A6 (PCXA_L006 exit 1)')]
json.dump(b, open('prov-p6s-20261109/PCXA_BUNDLES.json', 'w'), indent=1)
PY
