"""Remove only this job's rebuildable caches; retain all source/evidence/keys."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-5-20261027'
code='''from pathlib import Path
import os,json,hashlib,shutil
B=Path("'''+B+'''");live=[];deps=[];objects=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  comm=(p/'comm').read_text().strip();cmd=(p/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')
  if str(B) in cmd and comm in ['lean','cbmc','cargo','cargo-kani','kani-compiler','kani-driver','rustc']:live.append([int(p.name),comm,cmd])
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
for receipt in B.glob('LPe_L[0-9][0-9][0-9]/receipt.json'):
 r=json.loads(receipt.read_text())
 if r['exit_status']!=0:continue
 for x in r['deps_fingerprint']['selected_objects'].values():
  ok=hashlib.sha256(Path(x['path']).read_bytes()).hexdigest()==x['sha256'];deps.append(dict(path=x['path'],matches=ok))
for p in (B/'LPe_objects').rglob('*'):
 if p.is_file():objects.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
assert not live,live
assert all(x['matches'] for x in deps),deps
removed=[]
for name in ['LPe_target','LPe_objects','.lake']:
 p=B/name
 if p.exists():
  size=sum(x.stat().st_size for x in p.rglob('*') if x.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
tmp=[dict(path=str(p),mtime=p.stat().st_mtime,bytes=p.stat().st_size) for pattern in ['external-sat*.cnf','smt2_dec_problem*'] for p in Path('/tmp').glob(pattern)]
start=json.loads((B/'LPe_G001-reservation.json').read_text())['utc']
assert all(x['mtime']<start for x in tmp),'new solver temp requires ownership review'
out=dict(live_compilers_or_solvers=live,dependency_objects=deps,compiled_object_hashes=objects,removed_rebuildable_caches=removed,source_snapshots_retained=True,wallet_keys_touched=False,tmp_candidates=tmp,tmp_all_predate_job=True)
(B/'LPe_cleanup.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(dict(removed=removed,objects=len(objects),deps=len(deps),tmp=len(tmp))))
'''
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);print(r.stdout+r.stderr);assert r.returncode==0
subprocess.run(['scp','-q',H+':'+B+'/LPe_cleanup.json',str(E/'LPe_cleanup.json')],check=True)
