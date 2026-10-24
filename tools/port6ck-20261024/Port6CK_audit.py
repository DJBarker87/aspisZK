#!/usr/bin/env python3
"""Check final source/receipt/axiom policy and reuse assessments; no proof replay."""
from pathlib import Path
import hashlib,json,re,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/port6ck-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base='6394df23891e699f4db152110f727b7cac678184'
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert len(receipts)<=100
for r in receipts:
 assert r['limits']==limits and r['swaps']=='0',r['attempt']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 for name,digest in r['source_hashes'].items():assert sha(E/r['attempt']/'sources'/name)==digest
 if r['exit_status']==0:
  for ax in r['print_axioms']:
   names=re.search(r'depends on axioms: \[([^\]]*)\]',ax)
   assert names is None or set(names[1].split(', '))<={'propext','Classical.choice','Quot.sound'},ax
for p in E.glob('lean-*-reservation.json'):
 x=json.loads(p.read_text());assert x['reserved_bytes']+x['additional_bytes']<=x['limit_bytes']
final=next(r for r in reversed(receipts) if r['exit_status']==0 and 'Port6CK_Audit.lean' in r['source_hashes'])
accepted=[];theorems=[]
for src in sorted(L.glob('Port6CK_*.lean')):
 matches=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(src.name)==sha(src)]
 assert matches,src
 text=src.read_text();clean=re.sub(r'/-.*?-/', '', text, flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b',clean),src
 ns=re.search(r'^namespace (\S+)',clean,re.M)
 if ns:
  for name in re.findall(r'^theorem (\w+)',clean,re.M):theorems.append(ns[1]+'.'+name)
 accepted.append({'module':src.stem,'sha256':sha(src),'receipt':matches[-1]['attempt']})
for theorem in theorems:assert any("'"+theorem+"' " in line for line in final['print_axioms']),theorem
changes=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
allowed=('evidence/port6ck-20261024/','tools/port6ck-20261024/','docs/research/100bit-spend-path-20261013/lean/Port6CK_')
assert all(p.startswith(allowed) for p in changes),[p for p in changes if not p.startswith(allowed)]
for p in [R/name for name in changes]:
 if p.is_file():assert p.stat().st_size<=5_000_000,p
# Reuse means unchanged source matched to accepted historical receipts, not a new gate.
parents=[]
for job,prefix in [('port5q1-20261024','Port5Q1_'),('port5q2-20261024','Port5Q2_')]:
 old=R/'evidence'/job
 oldr=[(p,json.loads(p.read_text())) for p in old.glob('lean-*/receipt.json')]
 modules=[]
 for p in sorted(L.glob(prefix+'*.lean')):
  candidates=[(path,r) for path,r in oldr if r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
  assert candidates,p
  path,r=sorted(candidates)[-1]
  modules.append({'module':p.stem,'source_sha256':sha(p),'accepted_receipt':str(path.relative_to(R)),'receipt_sha256':sha(path)})
 parents.append({'job':job,'modules':modules,'status':'source-identical cached focused evidence; not a new identity gate'})
for name in ['raw','scalar','semantic','validate','weights']:
 old=R/'evidence/port5q2-20261024';x=json.loads((old/(name+'-emission.json')).read_text())
 assert x['source_sha256']==sha(old/'reader-helpers/Funs.lean')
 module={'raw':'ReaderRaw','scalar':'ReaderScalar','semantic':'ReaderSemantic','validate':'ReaderValidate','weights':'ReaderWeights'}[name]
 assert x['module_sha256']==sha(L/('Port5Q2_'+module+'.lean'))
 assert not x['external_template_imported']
(E/'parent-admission.json').write_text(json.dumps(parents,indent=2)+'\n')
# Inventory only OWN current workspace products. No parent/shared objects are overwritten.
remote='''from pathlib import Path
import hashlib,json
p=Path('/home/dombarker/project-offloads/codex-cx-port6ck-20261024')
rows={}
for f in p.glob('Port6CK_*.olean'):
 s=f.with_suffix('.lean');rows[f.name]={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size,'source_sha256':hashlib.sha256(s.read_bytes()).hexdigest()}
print(json.dumps(rows,indent=2))'''
x=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-c',shlex.quote(remote)],text=True))
for row in accepted:
 assert x[row['module']+'.olean']['source_sha256']==row['sha256'],row
for module in accepted:
 r=next(r for r in receipts if r['attempt']==module['receipt'])
 for key,row in r['deps_fingerprint']['selected_objects'].items():
  if key.startswith('Port6CK_') and key.endswith('.olean'):
   assert row['sha256']==x[key]['sha256'],(module['module'],key,'stale owned dependency')
for key,row in final['deps_fingerprint']['selected_objects'].items():
 if key.startswith('Port6CK_') and key.endswith('.olean'):
  assert row['sha256']==x[key]['sha256'],key
(E/'own-object-inventory.json').write_text(json.dumps(x,indent=2)+'\n')
manifest={'schema':'focused-extractor-proof-packet-v1','job':'port6ck-20261024','baseline_revision':base,'source_revision':revision,
 'accepted_modules':accepted,'top_theorems':theorems,'final_audit':final,'actual_lean_compiles':len(receipts),'lean_budget':100,
 'new_kani_runs':0,'kani_budget':40,'excluded_attempts':[r['attempt'] for r in receipts if r['exit_status']!=0],
 'not_entered_lean':['lean-008','lean-016'],'caps':limits,'parent_admission_sha256':sha(E/'parent-admission.json'),
 'validation':'focused modules, dependent bridges, one compatible-import/full axioms audit; no frozen release replay',
 'source_change_assessment':'only new Port6CK modules and own tools/evidence; shipped source, keys, source protocol/wire/features and release artifacts unchanged',
 'inherited_elf_pins':['f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548']}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','modules':len(accepted),'theorems':len(theorems),'actual_lean_compiles':len(receipts),'new_kani_runs':0,'protected_source_changes':[]}))
