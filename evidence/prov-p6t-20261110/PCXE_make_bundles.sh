#!/bin/bash
# PCXE_make_bundles.sh: NEW compile vehicles PRVCmb_C14.. for the credited files that are new relative to PCXB_ (PCXE_CREDITED_FILES.json new_relative_to_PCXB).
# C01..C12 are the PCXB_ bundles byte for byte (copied), C13 is the PCXC_ corrected bundle (native.decide declaration removed). Same rule PCXB-C2 (PCXE_rename.py) with PCXE-C4 (PCVB_ helper namespaces).
set -e
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t
python3 -I -B - <<'PY'
D = 'evidence/prov-p6t-20261110'
import json, subprocess, sys, hashlib
sys.dont_write_bytecode = True
sys.path.insert(0, D)
import PCXE_rename as R
cf = json.load(open(f'{D}/PCXE_CREDITED_FILES.json'))
new = cf['new_relative_to_PCXB']; by = {f['path']: f for f in cf['files']}
def show(p): return subprocess.check_output(['git', 'show', 'HEAD:' + p]).decode()
rest = sorted(new); groups = []; cur = []; sz = 0
for p in rest:
    if sz + by[p]['bytes'] > 200000 and cur: groups.append(cur); cur = []; sz = 0
    cur.append(p); sz += by[p]['bytes']
if cur: groups.append(cur)
out = []
for k, fl in enumerate(groups, 18):
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
        stack = []
        for l in txt.split('\n'):
            s = l.strip()
            if s.startswith('namespace '): stack.append(s)
            elif s.startswith('noncomputable section'): stack.append(s)
            elif s.startswith('section'): stack.append(s)
            elif s == 'end' or s.startswith('end '):
                if stack: stack.pop()
        closers = []
        for s in reversed(stack):
            if s.startswith('namespace '): closers.append('end ' + s.split()[1])
            elif s.startswith('noncomputable section'): closers.append('end')
            else: closers.append('end' + (' ' + s.split()[1] if len(s.split()) > 1 else ''))
        body += [f'section PRVBundle_{j}', txt] + closers + [f'end PRVBundle_{j}']
    imps = [l for l in imports if l == 'import Aeneas'] + [l for l in imports if l != 'import Aeneas']
    hdr = [f'-- PCXE combined-import bundle {nm}: exact file texts (import lines hoisted), declared names renamed by PCXE_rename.py tag C{k:02d}_Fjj (rules PCXB-C2, PCXE-C4): ' + ', '.join(x.split('/')[-1] for x in fl)] + imps + ['']
    text = '\n'.join(hdr) + '\n'.join(body) + '\n'
    open(f'{D}/{nm}.lean', 'w').write(text)
    out.append(dict(bundle=nm, files=fl, bytes=len(text), tags={f: f'C{k:02d}_F{j:02d}' for j, f in enumerate(fl)})); print(nm, len(fl), len(text))
old = json.load(open('evidence/prov-p6r-20261110/PCXD_BUNDLES.json'))['bundles']
allb = [dict(b, source=b.get('source','PCXD_ (byte-identical copy)')) for b in old] + [dict(b, source='PCXE_ new') for b in out]
names = [b['bundle'] for b in allb]
auditdef = open(f'{D}/PCXE_audit_def.lean.in').read()
root = ['-- PCXE_ROOT: the one root module of the combined import. Imports every bundle (and the generic helper PRVH_WrapAdd), then one audit pass over every constant under PRV*/PCVE*/PCVB*.', 'import Aeneas', 'import Lean', 'import PRVH_WrapAdd'] + [f'import {n}' for n in names] + ['']
open(f'{D}/PRVCmb_ROOT.lean', 'w').write('\n'.join(root) + auditdef + '\n#eval PRVCmbAudit.auditRoot "PRV*/PCVE*/PCVB*" (fun n => let r := n.getRoot.toString; r.startsWith "PRV" || r.startsWith "PCVE" || r.startsWith "PCVB" || (n.toString.splitOn ".PRVEq.").length > 1 || (n.toString.splitOn ".PRVFresh_").length > 1)\n')
json.dump(dict(rule='PCXB-C2 + PCXE-C4', bundles=allb), open(f'{D}/PCXE_BUNDLES.json', 'w'), indent=1)
PY
