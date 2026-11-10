#!/bin/bash
# PCXD_make_bundles.sh: NEW compile vehicles PRVCmb_C14.. for the credited files that are new relative to PCXB_ (PCXD_CREDITED_FILES.json new_relative_to_PCXB).
# C01..C12 are the PCXB_ bundles byte for byte (copied), C13 is the PCXC_ corrected bundle (native.decide declaration removed). Same rule PCXB-C2 (PCXD_rename.py) with PCXD-C4 (PCVB_ helper namespaces).
set -e
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r
python3 -I -B - <<'PY'
D = 'evidence/prov-p6r-20261110'
import json, subprocess, sys, hashlib
sys.dont_write_bytecode = True
sys.path.insert(0, D)
import PCXD_rename as R
cf = json.load(open(f'{D}/PCXD_CREDITED_FILES.json'))
new = cf['new_relative_to_PCXB']; by = {f['path']: f for f in cf['files']}
def show(p): return subprocess.check_output(['git', 'show', 'HEAD:' + p]).decode()
rest = sorted(new); groups = []; cur = []; sz = 0
for p in rest:
    if sz + by[p]['bytes'] > 200000 and cur: groups.append(cur); cur = []; sz = 0
    cur.append(p); sz += by[p]['bytes']
if cur: groups.append(cur)
out = []
for k, fl in enumerate(groups, 14):
    nm = f'PRVCmb_C{k:02d}'; imports = []; body = []; imports_f = {}
    for j, f in enumerate(fl):
        keep = []; imports_f[f] = []
        for l in show(f).split('\n'):
            if l.startswith('import '):
                imports_f[f].append(l)
                if l not in imports: imports.append(l)
            else: keep.append(l)
        nc = any(l.strip() == 'noncomputable section' for l in keep)
        tag = f'C{k:02d}_F{j:02d}'
        txt = R.rename('\n'.join(keep), tag, 'import PRVH_WrapAdd' in imports_f[f])
        body += [f'section PRVBundle_{j}', txt] + (['end'] if nc else []) + [f'end PRVBundle_{j}']
    imps = [l for l in imports if l == 'import Aeneas'] + [l for l in imports if l != 'import Aeneas']
    hdr = [f'-- PCXD combined-import bundle {nm}: exact file texts (import lines hoisted), declared names renamed by PCXD_rename.py tag C{k:02d}_Fjj (rules PCXB-C2, PCXD-C4): ' + ', '.join(x.split('/')[-1] for x in fl)] + imps + ['']
    text = '\n'.join(hdr) + '\n'.join(body) + '\n'
    open(f'{D}/{nm}.lean', 'w').write(text)
    out.append(dict(bundle=nm, files=fl, bytes=len(text), tags={f: f'C{k:02d}_F{j:02d}' for j, f in enumerate(fl)})); print(nm, len(fl), len(text))
old = json.load(open('evidence/prov-p6c-20261109/PCXB_BUNDLES.json'))['bundles']
allb = [dict(b, source='PCXB_ (byte-identical copy)' if b['bundle'] != 'PRVCmb_C13' else 'PCXC_ corrected copy (native.decide declaration removed)') for b in old] + [dict(b, source='PCXD_ new') for b in out]
names = [b['bundle'] for b in allb]
auditdef = open(f'{D}/PCXD_audit_def.lean.in').read()
root = ['-- PCXD_ROOT: the one root module of the combined import. Imports every bundle (and the generic helper PRVH_WrapAdd), then one audit pass over every constant under PRV*/PCVE*/PCVB*.', 'import Aeneas', 'import Lean', 'import PRVH_WrapAdd'] + [f'import {n}' for n in names] + ['']
open(f'{D}/PRVCmb_ROOT.lean', 'w').write('\n'.join(root) + auditdef + '\n#eval PRVCmbAudit.auditRoot "PRV*/PCVE*/PCVB*" (fun n => let r := n.getRoot.toString; r.startsWith "PRV" || r.startsWith "PCVE" || r.startsWith "PCVB")\n')
json.dump(dict(rule='PCXB-C2 + PCXD-C4', bundles=allb), open(f'{D}/PCXD_BUNDLES.json', 'w'), indent=1)
PY
