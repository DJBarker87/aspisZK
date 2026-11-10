#!/bin/bash
# PCXB_make_bundles.sh [NBUNDLES]: build the audit compile vehicles from the credited proving files of PCUF_ALL_STATUS.json.
# Rule (recorded in PCXB_CLASSIFICATIONS.json PCXB-C1): a file is credited iff it is the proving_file of a PROVED* record with a correct basis.
# Files that declare a common fully-qualified name are never placed in one bundle (no renaming: renaming a gate-namespace file changes name resolution).
set -e
N=${1:-8}
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence
python3 -I - "$N" <<'PY'
import json, sys, re, collections, importlib.util
sys.dont_write_bytecode = True
N = int(sys.argv[1])
spec = importlib.util.spec_from_file_location('P', 'prov-p0-20261109/PCO_partition.py'); P = importlib.util.module_from_spec(spec); spec.loader.exec_module(P)
s = json.load(open('prov-p2f-20261109/PCUF_ALL_STATUS.json'))
recs = [d for m in s['modules'].values() for d in m.values()]
good = [r for r in recs if r['status'].startswith('PROVED') and not r['basis_not_correct']]
files = sorted(set(r['proving_file'] for r in good))
size = {f: len(open(f).read()) for f in files}
names = {f: set(n for n, k in P.decls(open(f).read())) for f in files}
bundles = [dict(files=[], size=0, names=set()) for _ in range(N)]
for f in sorted(files, key=lambda f: -size[f]):
    ok = [b for b in bundles if not (b['names'] & names[f])]
    b = min(ok, key=lambda b: b['size'])
    b['files'].append(f); b['size'] += size[f]; b['names'] |= names[f]
AUDIT = '''
section PRVAudit
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ns := env.constants.map₂.foldl (fun (acc : Array (Name × String)) n ci =>
    if n.getRoot == `PRVEq && !n.isInternal then
      acc.push (n, match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "AXIOM" | .opaqueInfo _ => "opaque" | _ => "other")
    else acc) #[]
  let ns := ns.qsort (fun a b => Name.lt a.1 b.1)
  let mut cnt := 0
  for (n, kind) in ns do
    let ax ← collectAxioms n
    cnt := cnt + 1
    IO.println s!"PRVEQ_KIND {n} {kind}"
    if ax.isEmpty then IO.println s!"'{n}' does not depend on any axioms"
    else IO.println s!"'{n}' depends on axioms: {ax.toList}"
  IO.println s!"PRVEQ_AUDIT_COUNT {cnt}"
  let loc := env.constants.map₂.foldl (fun (acc : Array Name) n ci => match ci with | .axiomInfo _ => acc.push n | _ => acc) #[]
  IO.println s!"PRVEQ_LOCAL_AXIOM_DECLS {loc.size} {loc.toList}"
end PRVAudit
'''
out = []
for i, b in enumerate(bundles):
    fl = sorted(b['files'])
    imports = []; body = []
    for j, f in enumerate(fl):
        keep = []
        for l in open(f).read().split('\n'):
            if l.startswith('import '):
                if l not in imports: imports.append(l)
            else: keep.append(l)
        noncomp = any(l.strip() == 'noncomputable section' for l in keep)
        body.append(f'section PRVBundle_{j}'); body.append('\n'.join(keep))
        if noncomp: body.append('end')
        body.append(f'end PRVBundle_{j}')
    imps = [l for l in imports if l == 'import Aeneas'] + [l for l in imports if l != 'import Aeneas']
    hdr = ['-- PCXB audit bundle A%d (compile vehicle only): exact concatenation of ' % (i + 1) + ', '.join(f.split('/')[-1] for f in fl)] + imps + ['']
    text = '\n'.join(hdr) + '\n'.join(body) + '\n' + AUDIT
    nm = f'PRVEq_bundle_A{i+1}'
    open(nm + '.lean', 'w').write(text)
    out.append(dict(bundle=nm, files=fl, bytes=len(text), n_files=len(fl)))
    print(nm, len(fl), len(text))
json.dump(dict(rule='PCXB-C1', n_credited_files=len(files), n_credited_definitions=len(good), bundles=out), open('PCXB_BUNDLES.json', 'w'), indent=1)
PY
mv PRVEq_bundle_A*.lean prov-p6c-20261109/ 2>/dev/null; mv PCXB_BUNDLES.json prov-p6c-20261109/
