#!/bin/bash
# PCXB_make_extra_bundles.sh: audit vehicles for the P4b (A9) and P4c (A10) final PRVEq files. These dirs are outside the sparse checkout and
# are read with `git show HEAD:<path>` (no widening of the sparse list). Same bundle layout and audit section as PCXB_make_bundles.sh.
set -e
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence
python3 -I - <<'PY'
import subprocess, json, re
audit = open('prov-p6c-20261109/PRVEq_bundle_A1.lean').read().split('\nsection PRVAudit\n', 1)[1]
audit = '\nsection PRVAudit\n' + audit
sets = {
 'A9': ['evidence/prov-p4b-20261109/PRVEq_NHV_NEO_WindowV2_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_NHV_NEO_ParserRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_NHV_NEB_AdditiveRef_Funs.lean',
        'evidence/prov-p4b-20261109/PRVEq_MultiproofConeRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_MultiproofSortRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_MultiproofParserRef_Funs.lean'],
 'A10': ['evidence/prov-p4c-20261109/PRVEq_AspisR1WithdrawalCaller_Funs.lean', 'evidence/prov-p4c-20261109/PRVEq_AspisR1SemanticCallExtraction_Funs.lean',
         'evidence/prov-p4c-20261109/PRVEq_AspisR1BatchedWeightsExtraction_Funs.lean', 'evidence/prov-p4c-20261109/PRVEq_NJT_ClaimsRef_Funs.lean']}
res = []
for nm, fl in sets.items():
    imports = []; body = []; blobs = {}
    for j, f in enumerate(fl):
        raw = subprocess.check_output(['git', 'show', 'HEAD:' + f]).decode()
        blobs[f] = subprocess.check_output(['git', 'rev-parse', 'HEAD:' + f]).decode().strip()
        keep = []
        for l in raw.split('\n'):
            if l.startswith('import '):
                if l not in imports: imports.append(l)
            else: keep.append(l)
        noncomp = any(l.strip() == 'noncomputable section' for l in keep)
        body.append(f'section PRVBundle_{j}'); body.append('\n'.join(keep))
        if noncomp: body.append('end')
        body.append(f'end PRVBundle_{j}')
    imps = [l for l in imports if l == 'import Aeneas'] + [l for l in imports if l != 'import Aeneas']
    hdr = [f'-- PCXB audit bundle {nm} (compile vehicle only): exact concatenation of ' + ', '.join(f.split('/')[-1] for f in fl)] + imps + ['']
    text = '\n'.join(hdr) + '\n'.join(body) + '\n' + audit
    open(f'prov-p6c-20261109/PRVEq_bundle_{nm}.lean', 'w').write(text)
    res.append(dict(bundle='PRVEq_bundle_' + nm, files=fl, git_blobs=blobs, bytes=len(text)))
    print(nm, len(text))
json.dump(res, open('prov-p6c-20261109/PCXB_BUNDLES_EXTRA.json', 'w'), indent=1)
PY
