#!/bin/bash
# PCXB_make_bundles.sh: compile vehicles for the combined import from PCXB_CREDITED_FILES.json.
# Namespace rule (PCXB-C2, deterministic, textual; see PCXB_rename.py): the j-th credited file (path order) of bundle PRVCmb_Ckk has its declared PRVEq./PRVFresh_/helper-namespace names suffixed by the tag Ckk_Fjj
# (an outer wrapping namespace was tried first and rejected: it breaks resolution of gate names through the file's own `namespace X`, PCXB_L004).
# Bundles are separate modules (PRVCmb_Ckk); PRVCmb_ROOT imports them all and audits every PRVEq/PRVH/PRVC/PCVE constant.
set -e
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c
D0='evidence/prov-p6c-20261109'
python3 -I -B - <<'PY'
D0='evidence/prov-p6c-20261109'
import json, subprocess, sys
sys.dont_write_bytecode = True
sys.path.insert(0, D0)
import PCXB_rename as R
D = 'evidence/prov-p6c-20261109'
cf = json.load(open(f'{D}/PCXB_CREDITED_FILES.json'))['files']
def show(p): return subprocess.check_output(['git', 'show', 'HEAD:' + p]).decode()
S8 = 'evidence/prov-p4a-20261109/eq/PRVEq_S8OwnedP6_Funs.lean'
BIG = 'evidence/prov-p3d-20261109/PRVEq_RPu_FIq_Native07_P3b.lean'
P4B = [f['path'] for f in cf if '/prov-p4b-' in f['path']]; P4C = [f['path'] for f in cf if '/prov-p4c-' in f['path']]
rest = sorted((f for f in cf if f['path'] not in [S8, BIG] + P4B + P4C), key=lambda f: f['path'])
groups = [[S8], [BIG], P4B, P4C]
cur = []; sz = 0
for f in rest:
    if sz + f['bytes'] > 420000 and cur: groups.append(cur); cur = []; sz = 0
    cur.append(f['path']); sz += f['bytes']
if cur: groups.append(cur)
auditdef = open(f'{D}/PCXB_audit_def.lean.in').read()
out = []
for k, fl in enumerate(groups, 1):
    nm = f'PRVCmb_C{k:02d}'; imports = []; body = []
    imports_f = {}
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
    hdr = [f'-- PCXB combined-import bundle {nm}: exact file texts (import lines hoisted), with declared names renamed by PCXB_rename.py tag C{k:02d}_Fjj (rule PCXB-C2): ' + ', '.join(x.split('/')[-1] for x in fl)] + imps + ['']
    text = '\n'.join(hdr) + '\n'.join(body) + '\n'
    open(f'{D}/{nm}.lean', 'w').write(text)
    out.append(dict(bundle=nm, files=fl, bytes=len(text), tags={f: f'C{k:02d}_F{j:02d}' for j, f in enumerate(fl)}))
    print(nm, len(fl), len(text))
root = ['-- PCXB_ROOT: the one root module of the combined import. Imports every bundle (and the generic helper PRVH_WrapAdd), then one audit pass over every constant under PRVCmb.', 'import Aeneas', 'import Lean', 'import PRVH_WrapAdd'] + [f'import {b["bundle"]}' for b in out] + ['']
open(f'{D}/PRVCmb_ROOT.lean', 'w').write('\n'.join(root) + auditdef + '\n#eval PRVCmbAudit.auditRoot "PRV*/PCVE*" (fun n => let r := n.getRoot.toString; r.startsWith "PRV" || r.startsWith "PCVE")\n')
# audit self-test module: same definitions, run on the helper module's namespace
open(f'{D}/PRVCmb_AuditTest.lean', 'w').write('import Aeneas\nimport Lean\nimport PRVH_WrapAdd\n' + auditdef + '\n#eval PRVCmbAudit.auditRoot "PRVH" (fun n => let r := n.getRoot.toString; r.startsWith "PRV" || r.startsWith "PCVE")\n')
open(f'{D}/PRVH_WrapAdd.lean', 'w').write(show('evidence/prov-p1h-20261109/PRVH_WrapAdd.lean'))
json.dump(dict(rule='PCXB-C2', bundles=out), open(f'{D}/PCXB_BUNDLES.json', 'w'), indent=1)
PY
