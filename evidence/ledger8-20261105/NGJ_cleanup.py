from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-ledger8-20261105';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104';H='dombarker@100.108.41.90'
exports=json.loads((E/'NGJ_EXPORT.json').read_text())['exports'];graphs={p.name.removeprefix('NGJ_').removesuffix('.sha256'):p.read_text().strip() for p in E.glob('NGJ_NEP_*_REACHABLE.txt.sha256')}
code='''from pathlib import Path
import json,hashlib,subprocess
b=Path(B);c=Path(C)
for r in exports:
 p=Path(r['path']);assert p.is_relative_to(c) and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
removed=[]
for n,h in graphs.items():
 p=b/n
 if p.exists():
  assert p.is_relative_to(b) and hashlib.sha256(p.read_bytes()).hexdigest()==h,str(p)
  removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=h));p.unlink()
for folder in ['NGJ_objects','NGJ_native']:
 for p in (b/folder).iterdir():
  if not p.is_file():continue
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert any(r['sha256']==h and Path(r['path']).name==p.name for r in exports),str(p)
  removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=h));p.unlink()
ps=subprocess.check_output(['ps','-eo','pid,args'],text=True);active=[l for l in ps.splitlines() if B+'/' in l and any(w in l for w in ['/lean ','/leanc ','NGJ_ProofDriver','NGJ_PoolProofDriver','NGJ_Driver','NGJ_PoolDriver'])]
assert not active,active
report=dict(exports_checked=len(exports),cache_retained=str(c),removed_owned_rebuildable=removed,removed_bytes=sum(r['bytes'] for r in removed),active_owned_provers=active,disk=subprocess.check_output(['df','-h',str(c)],text=True),key_wallet_actions=0)
(b/'NGJ_HOST_END.json').write_text(json.dumps(report,indent=1)+'\\n');print(json.dumps(report))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nexports='+repr(exports)+'\ngraphs='+repr(graphs)+'\n'+code,capture_output=True,text=True);(E/'NGJ_CLEANUP_TRANSPORT.log').write_text(r.stderr);assert r.returncode==0,r.stderr;(E/'NGJ_HOST_END.json').write_text(r.stdout);d=json.loads(r.stdout);print('Cleaned own rebuildable bytes',d['removed_bytes'],'cache retained')
