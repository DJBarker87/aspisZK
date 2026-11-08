"""Check-only preflight for the amended immutable gate inputs; never overwrite them.
The earlier WIP generator selected stale source snapshots and omitted the shared
rev4 owners. This replacement enforces the final pins and pre-split root plan.
"""
from pathlib import Path
import json,lzma,re,hashlib,sys
assert sys.argv[1:]==['--check'],'Only --check is supported; gate inputs must be reviewed before replacement'
E=Path(__file__).resolve().parent;P=E.parent/'ledger28-20261111';N=E.parent/'tx1-principal-20261111';X=E.parent/'tx2-auth-20261111';B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111'
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
prior=J(P/'NNL_AUDIT_ROOTS.json');extra={r for g in J(N/'NNG_Resume_AUDIT_ROOTS.json')['groups']for r in g}
for name in ['NMX_R4','NMX_R6','NMX_R9']:
 x=J(X/(name+'_AUDIT_ROOTS.json'));extra.update(x.get('roots',[]));extra.update(r for g in x['groups']for r in g)
own=['NNM_Domains.'+n for n in ['exact345','exact344','exact233','exact242','exact241','domain345','domain344','domain233','domain242']]
new=sorted(extra-set(prior['roots']));tail=[r for g in prior['groups'][51:]for r in g]+new+own
initial=prior['groups'][:51]+[tail[i:i+120]for i in range(0,len(tail),120)]
paired=initial[:44]+[initial[i]+initial[i+1]for i in range(44,58,2)]
plan=J(E/'NNM_FINAL_SCOPE_PLAN.json');groups=paired[:47]+[J(E/'NNM_AUDIT_ROOTS.json')['groups'][i]for i in range(47,50)]+[plan['pending_roots']]
assert set(r for g in groups[47:]for r in g)==set(r for g in paired[47:]for r in g)
required=J(E/'NNM_AUDIT_ROOTS.json');assert required['roots']==sorted(set(prior['roots'])|extra|set(own))
assert required['groups'][:51]==groups
assert set(r for g in required['groups'][51:]for r in g)<=set(groups[50])
assert len(groups)==51 and len(required['roots'])==13715
assert sum(map(len,groups))==len({r for g in groups for r in g})==13715
for window in plan['scopes']:assert window['root_names']==groups[window['group']]
assert J(E/'NNM_AUDIT_MODULES.json')==[['NNM_COMBINED_IMPORT']]*len(required['groups'])
assert J(E/'NNM_PATHS.json')[0]==B+'/NNM_exports_final_20261111'
assert J(E/'NNM_PATHS.json')[1:6]==[B+'/'+n for n in ['NNM_rev4','NNM_tx1','NNM_wrapperR4','NNM_tx2','NNM_previous']]
cfg=J(E/'NNM_SEED_CONFIG.json');assert len(cfg['wrapper_modules'])==15 and all(m.startswith('NMV_')for m in cfg['wrapper_modules'])
assert all(r['module'].startswith(('NMX_','NMS_','LIBB_'))for r in cfg['tx2_objects'])
plan=J(E/'NNM_COHERENCE_PLAN.json')
for p in(E/'NNM_rev4_sources').glob('*.lean'):
 assert p.read_bytes()==(E.parent/'rowspec-lead-20261107'/p.name).read_bytes()
 assert hashlib.sha256(p.read_bytes()).hexdigest()==plan['modules'][p.stem]
expected={x['module']:x['imports']for l in(E/'NNM_EXPECTED_IMPORTS.jsonl').read_text().splitlines()if(x:=json.loads(l))}
loaded=[json.loads(l)for l in(E/'NNM_LOADED_scan.jsonl').read_text().splitlines()]
for row in loaded:
 assert row['imports_match']and not row['dangling']and not row['duplicate_owners']
 assert expected[row['module']]==row['imports']
 # Independent current source imports for the changed supplier families.
 m=row['module'];paths=[folder/(m+'.lean')for folder in [E,E/'NNM_rev4_sources',N,X,E.parent/'tx2-owned-20261111']]
 p=next((p for p in paths if p.exists()),None)
 if p is not None:
  imports=list(dict.fromkeys(['Init']+re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M)))
  assert expected[m]==imports,(m,imports,expected[m])
print(f'NNM amended preflight PASS:13715 required roots,51 original groups,{len(required["groups"])-51} continuation groups,single rev4 source set,15 refreshed NMV modules,current source-derived import inventory')
