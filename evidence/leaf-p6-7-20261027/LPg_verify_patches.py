from pathlib import Path
import subprocess,json,tempfile,hashlib
E=Path(__file__).resolve().parent
S='crates/aspis-r1-cost-probe/src/'
parents=[S+x+'.rs' for x in ['fast_pairing','compact','verifier','r1_wire','candidate']]
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('LPg_K*/receipt.json'))]
rels=sorted({f.removeprefix('LPg_src/') for r in receipts for f in r['source_hashes'] if f.startswith('LPg_src/')})
code='''from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027/LPc_src')
parents='''+repr(parents)+'''\nrels='''+repr(rels)+'''
print(json.dumps({'parents':{p:(B/p).read_text() for p in parents},'base_hashes':{p:hashlib.sha256((B/p).read_bytes()).hexdigest() for p in rels if (B/p).is_file()}}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90',"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True);base=json.loads(r.stdout)
checks=[];errors=[]
for r in receipts:
 a=r['attempt'];p=E/(a+'-harness.patch')
 if not p.exists():errors.append(a+' missing patch');continue
 info=json.loads((E/(a+'-patch.json')).read_text())
 if hashlib.sha256(p.read_bytes()).hexdigest()!=info['sha256']:errors.append(a+' patch hash')
 with tempfile.TemporaryDirectory(prefix='LPg_patch_check_') as td:
  d=Path(td)
  for rel,text in base['parents'].items():
   q=d/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(text)
  ap=subprocess.run(['git','apply',str(p)],cwd=d,capture_output=True,text=True)
  if ap.returncode:errors.append(a+' apply '+ap.stderr);continue
  for f,sha in r['source_hashes'].items():
   rel=f.removeprefix('LPg_src/');q=d/rel
   actual=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else base['base_hashes'].get(rel)
   if actual!=sha:errors.append(a+' source '+rel)
  checks.append(a)
(E/'LPg_PATCH_VERIFICATION.json').write_text(json.dumps({'checked_attempts':checks,'errors':errors,'method':'git apply each committed per-run patch to the five exact LPc K020 parent sources; compare every source hash against reconstruction or unchanged inherited base'},indent=2)+'\n')
print('patch checks',len(checks),'errors',len(errors));assert not errors,errors
