#!/bin/bash
# PCXB_credited.sh: PCXB_CREDITED_FILES.json = the credited Lean files of the combined import, derived from PCQH_ALL_STATUS.json.
# Credit rule (PCXB-C1): a file is credited iff it is the proving_file of an EQUALITY_PROVED / EQUALITY_DOMAIN / CONDITIONAL_ON_BINDING record of PCQH_ALL_STATUS.json
# (those statuses already encode the correct-basis selection), or, for the 93 records without proving_file, the file that declares the record's theorem in the P2g finals
# (65) or the P4b/P4c final PRVEq files (28, module-level records of PCXA). Plus the generic lemma modules named in the handoffs. Files are read with git show HEAD:<path>.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c
python3 -I -B - <<'PY'
import json, collections, subprocess, re, sys, importlib.util
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('P', 'evidence/prov-p0-20261109/PCO_partition.py'); P = importlib.util.module_from_spec(spec); spec.loader.exec_module(P)
SCR = '/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partc'
paths = [l.strip() for l in open(SCR + '/all_lean_paths.txt')]
by = collections.defaultdict(list)
for p in paths: by[p.split('/')[-1]].append(p)
def show(p): return subprocess.run(['git', 'show', 'HEAD:' + p], capture_output=True).stdout.decode()
d = json.load(open('evidence/prov-p1h-20261109/PCQH_ALL_STATUS.json'))
PH = {'P1h':'prov-p1h','P2h':'prov-p2h','P3a':'prov-p3a','P3b':'prov-p3b','P3c':'prov-p3c','P3d':'prov-p3d','P4e':'prov-p4e','P2f':'prov-p2f','P2r':'prov-p2r','P5':'prov-p5','P2a':'prov-p2a','P2b':'prov-p2b','P2c':'prov-p2c','P2d':'prov-p2d','P2g':'prov-p2g','P4a':'prov-p4a','P4c':'prov-p4c','P4b':'prov-p4b'}
CRED = {'EQUALITY_PROVED', 'EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING'}
def resolve(pf, phase):
    if pf in paths: return pf
    cand = [c for c in by.get(pf.split('/')[-1], []) if c.endswith(pf)]
    cand = [c for c in cand if not re.search(r'/(gen|probe|failed_shapes)|PC[A-Z]{2,3}_L\d|/sources/|ingested', c)]
    if len(cand) == 1: return cand[0]
    ph = PH.get(phase); c2 = [c for c in cand if ph and f'/{ph}-' in c]
    if len(c2) == 1: return c2[0]
    return None
files = collections.defaultdict(lambda: dict(records=0, statuses=collections.Counter(), phases=set(), theorems=[]))
unres = []; nofile = []
for m, dd in d['modules'].items():
    for n, r in dd.items():
        if r['status'] not in CRED: continue
        pf = r.get('proving_file')
        if not pf: nofile.append((m, n, r)); continue
        p = resolve(pf, r['decided_by'])
        if not p: unres.append((m, n, pf, r['decided_by'])); continue
        f = files[p]; f['records'] += 1; f['statuses'][r['status']] += 1; f['phases'].add(r['decided_by']); f['theorems'].append(r['theorem'])
# records without proving_file: by declared theorem in the P2g finals; PCXA module-level (theorem None) -> P4b/P4c finals
p2g = [p for p in paths if re.match(r'evidence/prov-p2g-20261109/PRVEq_[^/]*\.lean$', p) and 'bundle' not in p and 'diag' not in p]
idx = collections.defaultdict(set)
for p in p2g:
    for nm, k in P.decls(show(p)): idx[nm].add(p)
lost = []
for m, n, r in nofile:
    th = (r['theorem'] or '').split(' ;')[0].split(' (+')[0].strip()
    fs = idx.get(th, set()) | idx.get(th + '.equiv', set())
    if fs:
        for p in fs:
            f = files[p]; f['records'] += 1; f['statuses'][r['status']] += 1; f['phases'].add(r['decided_by']); f['theorems'].append(th)
    else: lost.append((m, n, r['decided_by']))
P4 = ['evidence/prov-p4b-20261109/PRVEq_NHV_NEO_WindowV2_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_NHV_NEO_ParserRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_NHV_NEB_AdditiveRef_Funs.lean',
      'evidence/prov-p4b-20261109/PRVEq_MultiproofConeRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_MultiproofSortRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_MultiproofParserRef_Funs.lean',
      'evidence/prov-p4c-20261109/PRVEq_AspisR1WithdrawalCaller_Funs.lean', 'evidence/prov-p4c-20261109/PRVEq_AspisR1SemanticCallExtraction_Funs.lean',
      'evidence/prov-p4c-20261109/PRVEq_AspisR1BatchedWeightsExtraction_Funs.lean', 'evidence/prov-p4c-20261109/PRVEq_NJT_ClaimsRef_Funs.lean']
for p in P4:
    assert p in paths, p
    f = files[p]; f['phases'].add('PCXA(P4b/P4c module-level)')
GEN = ['evidence/prov-p2h-20261109/PRVEq_const_bind.lean', 'evidence/prov-p1h-20261109/PRVH_Shift.lean', 'evidence/prov-p1h-20261109/PRVH_LoopDom.lean', 'evidence/prov-p1h-20261109/PRVC_LoopBridge.lean']
for p in GEN:
    assert p in paths, p
    files[p]['phases'].add('generic lemma module')
rows = []
for p, v in sorted(files.items()):
    t = show(p)
    rows.append(dict(path=p, bytes=len(t), blob=subprocess.run(['git', 'rev-parse', 'HEAD:' + p], capture_output=True).stdout.decode().strip(), records=v['records'], statuses=dict(v['statuses']), phases=sorted(v['phases']),
                     has_sorry=bool(re.search(r'\bsorry\b', t)), has_native_decide=('native_decide' in t), has_axiom_decl=bool(re.search(r'(?m)^\s*axiom\s', t)),
                     imports=[l[7:].strip() for l in t.split('\n') if l.startswith('import ')]))
print(len(rows), 'files;', sum(r['bytes'] for r in rows), 'bytes;', 'unresolved', unres[:5], 'lost', lost)
print('flags', [r['path'] for r in rows if r['has_sorry'] or r['has_native_decide'] or r['has_axiom_decl']])
json.dump(dict(schema='PCXB_CREDITED_FILES/1', rule='PCXB-C1', n_files=len(rows), unresolved_records=unres, records_without_file_not_found=lost, files=rows), open('evidence/prov-p6c-20261109/PCXB_CREDITED_FILES.json', 'w'), indent=1)
PY
