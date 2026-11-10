#!/bin/bash
# PCXD_credited.sh: PCXD_CREDITED_FILES.json = credited Lean files, derived from PCUJ_ALL_STATUS.json (P2j status merged over PCUI, PCQH).
# Rule PCXD-C1 = PCXB-C1 (proving_file of an EQUALITY_PROVED / EQUALITY_DOMAIN / CONDITIONAL_ON_BINDING record; records without proving_file: the file declaring
# the record theorem in the P2g finals, the P2i individual files, or the P2j individual files), plus overlays: P3b V8R19 M31.mul (PCXD-C2), generic modules.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r
python3 -I -B - <<'PY'
import json, collections, subprocess, re, sys, importlib.util
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('P', 'evidence/prov-p0-20261109/PCO_partition.py'); P = importlib.util.module_from_spec(spec); spec.loader.exec_module(P)
SCR = sys.argv[1] if len(sys.argv) > 1 else None
SCR = '/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partd'
paths = [l.strip() for l in open(SCR + '/all_lean_paths.txt')]
by = collections.defaultdict(list)
for p in paths: by[p.split('/')[-1]].append(p)
def show(p): return subprocess.run(['git', 'show', 'HEAD:' + p], capture_output=True).stdout.decode()
d = json.load(open('evidence/prov-p2j-20261110/PCUJ_ALL_STATUS.json'))
PH = {'P1h':'prov-p1h','P2h':'prov-p2h','P3a':'prov-p3a','P3b':'prov-p3b','P3c':'prov-p3c','P3d':'prov-p3d','P4e':'prov-p4e','P2f':'prov-p2f','P2r':'prov-p2r','P5':'prov-p5','P2a':'prov-p2a','P2b':'prov-p2b','P2c':'prov-p2c','P2d':'prov-p2d','P2g':'prov-p2g','P4a':'prov-p4a','P4c':'prov-p4c','P4b':'prov-p4b','P2i':'prov-p2i','P2j':'prov-p2j'}
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
        if r['decided_by'] in ('P2i', 'P2j'): pf = None  # PCXD-C3: PCUI/PCUJ records carry a stale proving_file basename inherited from the superseded P5/P2 record; the file is found by theorem name inside that phase's directory
        if not pf: nofile.append((m, n, r)); continue
        p = resolve(pf, r['decided_by'])
        if not p: unres.append((m, n, pf, r['decided_by'])); continue
        f = files[p]; f['records'] += 1; f['statuses'][r['status']] += 1; f['phases'].add(r['decided_by']); f['theorems'].append(r['theorem'])
SRCDIRS = [r'evidence/prov-p2g-20261109/PRVEq_[^/]*\.lean$', r'evidence/prov-p2i-20261110/PRVEq_[^/]*\.lean$', r'evidence/prov-p2j-20261110/PRVEq_[^/]*\.lean$']
src = [p for p in paths if any(re.match(x, p) for x in SRCDIRS) and 'bundle' not in p and 'diag' not in p]
idx = collections.defaultdict(set)
for p in src:
    for nm, k in P.decls(show(p)): idx[nm].add(p)
lost = []
for m, n, r in nofile:
    th = (r['theorem'] or '').split(' ;')[0].split(' (+')[0].strip()
    ph = PH.get(r['decided_by'])
    fs = idx.get(th, set()) | idx.get(th + '.equiv', set())
    fs2 = {p for p in fs if ph and f'/{ph}-' in p}
    fs = fs2 or fs
    if fs:
        for p in fs:
            f = files[p]; f['records'] += 1; f['statuses'][r['status']] += 1; f['phases'].add(r['decided_by']); f['theorems'].append(th)
    else: lost.append((m, n, r['decided_by'], th))
P4 = ['evidence/prov-p4b-20261109/PRVEq_NHV_NEO_WindowV2_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_NHV_NEO_ParserRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_NHV_NEB_AdditiveRef_Funs.lean',
      'evidence/prov-p4b-20261109/PRVEq_MultiproofConeRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_MultiproofSortRef_Funs.lean', 'evidence/prov-p4b-20261109/PRVEq_MultiproofParserRef_Funs.lean',
      'evidence/prov-p4c-20261109/PRVEq_AspisR1WithdrawalCaller_Funs.lean', 'evidence/prov-p4c-20261109/PRVEq_AspisR1SemanticCallExtraction_Funs.lean',
      'evidence/prov-p4c-20261109/PRVEq_AspisR1BatchedWeightsExtraction_Funs.lean', 'evidence/prov-p4c-20261109/PRVEq_NJT_ClaimsRef_Funs.lean']
for p in P4:
    assert p in paths, p
    f = files[p]; f['phases'].add('PCXA(P4b/P4c module-level)')
GEN = ['evidence/prov-p6c-20261109/PRVEq_transport_row_P3.lean', 'evidence/prov-p2h-20261109/PRVEq_const_bind.lean', 'evidence/prov-p1h-20261109/PRVH_Shift.lean', 'evidence/prov-p1h-20261109/PRVH_LoopDom.lean', 'evidence/prov-p1h-20261109/PRVC_LoopBridge.lean']
for p in GEN:
    assert p in paths, p
    files[p]['phases'].add('generic lemma module or P3e (PCVE_) file')
# PCXD-C2 overlay: P3b (PCVB_L041-L043) V8R19 M31.mul full-equality files; credited for the three V8R19 M31.mul records (see PCXD_CLASSIFICATIONS.json)
P3B = ['evidence/prov-p3b-20261109/PRVEq_AspisV8R19_ComplexFieldSlice_P3.lean', 'evidence/prov-p3b-20261109/PRVEq_AspisV8R19_GuardedFieldSlice_P3.lean', 'evidence/prov-p3b-20261109/PRVEq_AspisV8R19_QuarticFieldSlice_P3.lean']
for p in P3B:
    assert p in paths, p
    f = files[p]; f['phases'].add('P3b overlay PCXD-C2'); f['records'] += 1
rows = []
for p, v in sorted(files.items()):
    t = show(p)
    rows.append(dict(path=p, bytes=len(t), blob=subprocess.run(['git', 'rev-parse', 'HEAD:' + p], capture_output=True).stdout.decode().strip(), records=v['records'], statuses=dict(v['statuses']), phases=sorted(v['phases']),
                     has_sorry=bool(re.search(r'\bsorry\b', t)), has_native_decide=('native_decide' in t), has_axiom_decl=bool(re.search(r'(?m)^\s*axiom\s', t)),
                     imports=[l[7:].strip() for l in t.split('\n') if l.startswith('import ')]))
print(len(rows), 'files;', sum(r['bytes'] for r in rows), 'bytes;', 'unresolved', unres[:8], 'lost', lost[:8])
print('flags', [r['path'] for r in rows if r['has_sorry'] or r['has_native_decide'] or r['has_axiom_decl']])
old = {f['path'] for f in json.load(open('evidence/prov-p6c-20261109/PCXB_CREDITED_FILES.json'))['files']}
new = sorted(set(r['path'] for r in rows) - old); gone = sorted(old - set(r['path'] for r in rows))
print('new', len(new)); [print('  +', x) for x in new]; print('gone', len(gone)); [print('  -', x) for x in gone]
json.dump(dict(schema='PCXD_CREDITED_FILES/1', rule='PCXD-C1', n_files=len(rows), unresolved_records=unres, records_without_file_not_found=lost, new_relative_to_PCXB=new, no_longer_credited_relative_to_PCXB=gone, files=rows), open('evidence/prov-p6r-20261110/PCXD_CREDITED_FILES.json', 'w'), indent=1)
PY
