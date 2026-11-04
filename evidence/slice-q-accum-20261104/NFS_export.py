"""Verify current accepted objects into the owned retained cache, then clean own outputs."""
from pathlib import Path
import json,subprocess,hashlib,time,sys
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-q-accum-20261104';C='/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104';H='dombarker@100.108.41.90'
manifest=json.loads((E/'NFS_AUDIT_ROOTS.json').read_text());modules=list(dict.fromkeys(manifest['new_modules']+['NFS_AccumPart00','NFS_AccumPart01','NFS_AccumPart02','NFS_Folds','NFS_COMBINED_IMPORT','NFS_ProofDriver','NFS_Driver']))
sources={m:dict(source=(E/(m+'.lean')).read_text(),sha256=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()) for m in modules}
rows=[json.loads(l) for l in (E/'NFS_ATTEMPTS.jsonl').read_text().splitlines()]
scopes=sorted({r['cgroup'] for r in rows if 'cgroup' in r})
code=f'''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path({B!r});c=Path({C!r});receipt=b/'NFS_EXPORT-admission.json'
with (b/'NFS_EXPORT-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(receipt)],stdout=f,stderr=subprocess.STDOUT)
p=receipt;print(p.read_text() if p.exists() else 'MISSING',flush=True)
if not p.exists():sys.exit(79)
a=json.loads(p.read_text())
if r.returncode!=0 or a.get('allowed') is not True:sys.exit(78)
active=[]
for scope in {scopes!r}:
 p=Path(scope)/'cgroup.procs'
 if p.exists() and p.read_text().strip():active.append(dict(cgroup=scope,pids=p.read_text().split()))
assert not active,active
root=c/'NFS_exports_20261104';root.mkdir(exist_ok=True);exports=[]
for m,x in json.loads({json.dumps(sources)!r}).items():
 original=b/'NFS_generated'/(m+'.lean');assert hashlib.sha256(original.read_bytes()).hexdigest()==x['sha256'],m
 out=root/(m+'.lean');out.write_text(x['source']);items=[]
 for suffix in ['.olean','.olean.private','.olean.server','.ir','.ilean']:
  p=b/'NFS_objects'/(m+suffix)
  if p.exists():
   q=root/(m+suffix);shutil.copyfile(p,q);h=hashlib.sha256(q.read_bytes()).hexdigest();assert h==hashlib.sha256(p.read_bytes()).hexdigest();items.append(dict(path=str(q),sha256=h,bytes=q.stat().st_size))
 assert any(x['path'].endswith('.olean') for x in items),m
 exports.append(dict(module=m,source_path=str(out),source_sha256=x['sha256'],files=items))
native=c/'NFS_native_20261104';native.mkdir(exist_ok=True);pins=[]
for p in (b/'NFS_native').iterdir():
 if p.is_file():
  q=native/p.name;shutil.copyfile(p,q);pins.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
# Only own rebuildable outputs; retained cache and source/receipt inputs untouched.
removed=[]
for name in ['NFS_objects','NFS_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
for p in (b/'NFS_native').iterdir():
 if p.is_file() and p.suffix!='.c':p.unlink();removed.append(str(p))
print(json.dumps(dict(export=str(root),cache_retained=str(c),objects=exports,native=pins,active_owned_scopes=active,removed_own_outputs=removed,shared_tmp_untouched=True,wallet_or_key_cleanup=False),indent=1))
'''
for k in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 (E/f'NFS_EXPORT-{k}.log').write_text(r.stdout[:2500]+r.stderr)
 if r.returncode==0:
  # Admission prints multiline JSON first; final export object starts at export.
  idx=r.stdout.index('{\n "export"');out=json.loads(r.stdout[idx:]);(E/'NFS_EXPORT.json').write_text(json.dumps(out,indent=1)+'\n');break
 if r.returncode==255:
  raise RuntimeError('Export may have started: recover read-only; never resubmit')
 if r.returncode==78 and k<10:time.sleep(180);continue
 if r.returncode==79 and k==0:time.sleep(30);continue
 raise RuntimeError(r.stderr+r.stdout)
else:raise RuntimeError('admission exhausted')
print('exported',len(out['objects']),'modules; retained cache; no active owned scopes')
