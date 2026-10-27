from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-12-20261027'
# The job created no wallet/account keys. Only named compiled caches and
# positively-owned solver scratch are eligible; sources/receipts are retained.
expected={}
for p in E.glob('LPn_L*/receipt.json'):
 r=json.loads(p.read_text())
 for name,v in r['deps_fingerprint']['selected_objects'].items():expected[v['path']]=v['sha256']
code='''from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path('''+repr(B)+''');expected='''+repr(expected)+'''
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
live=subprocess.run(['pgrep','-af',r'^(/usr/bin/)?python3 S2W_(run|lean)_host.py LPn_'],capture_output=True,text=True)
assert not live.stdout.strip(),live.stdout
checks={p:{'sha256':digest(Path(p)),'expected':sha} for p,sha in expected.items()}
assert all(v['sha256']==v['expected'] for v in checks.values())
(B/'LPn_DEPENDENCY_VERIFICATION.json').write_text(json.dumps({'objects':checks,'errors':[]},indent=2)+'\\n')
rows=[]
for name in ['LPn_target','LPn_objects','.lake']:
 d=B/name
 if not d.exists():continue
 files=[p for p in d.rglob('*') if p.is_file()]
 manifest={str(p.relative_to(d)):{'bytes':p.stat().st_size,'sha256':digest(p)} for p in files}
 rows.append({'path':str(d),'files':len(files),'bytes':sum(r['bytes'] for r in manifest.values()),'manifest_sha256':hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest(),'removed':True})
 shutil.rmtree(d)
solver=[]
for p in (B/'LPn_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  solver.append({'path':str(p),'bytes':p.stat().st_size,'sha256':digest(p)});p.unlink()
out={'caches':rows,'owned_solver_files_removed':solver,'no_live_own_prover':True,'wallet_keys_created_or_deleted':0,'sources_receipts_and_shared_caches':'retained; no shared path removed','dependency_hashes_checked':len(checks)}
(B/'LPn_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''
r=subprocess.run(['ssh',H,"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True)
print(r.stdout)
for name in ['LPn_CLEANUP.json','LPn_DEPENDENCY_VERIFICATION.json']:
 subprocess.run(['scp','-q',H+':'+B+'/'+name,str(E/name)],check=True)
