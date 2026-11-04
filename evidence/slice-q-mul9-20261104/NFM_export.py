from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (E/'NFM_ATTEMPTS.jsonl').read_text().splitlines()];last={}
for r in rows:
 if r['kind']=='lean' and r['exit_status']==0 and r.get('module') and ('NFM_generated/'+r['module']+'.lean') in r.get('source_hashes',{}):last[r['module']]=r
items=[]
for module,r in last.items():
 h=r['source_hashes']['NFM_generated/'+module+'.lean'];assert hashlib.sha256((E/(module+'.lean')).read_bytes()).hexdigest()==h
 items.append(dict(module=module,attempt=r['attempt'],source_sha256=h))
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul9-20261104');C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul9-cache-20261104')
with (B/'NFM_EXPORT-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NFM_EXPORT-admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((B/'NFM_EXPORT-admission.json').read_text())
if r.returncode!=0 or a.get('allowed') is not True:print(json.dumps(dict(exit=r.returncode,admission=a)));sys.exit(78)
items=json.loads(PAYLOAD);out=[]
for item in items:
 m=item['module'];source=B/'NFM_generated'/(m+'.lean');assert hashlib.sha256(source.read_bytes()).hexdigest()==item['source_sha256']
 p=B/'NFM_objects'/(m+'.olean');assert p.is_file()
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  q=C/'NFM_exports_20261104'/z.relative_to(B/'NFM_objects');q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(z.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copyfile(z,q)
  source_copy=C/'NFM_exports_sources_20261104'/(m+'.lean');source_copy.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,source_copy);assert hashlib.sha256(source_copy.read_bytes()).hexdigest()==item['source_sha256']
  out.append({**item,'source_cache':str(source_copy),'source':str(z),'destination':str(q),'sha256':h,'bytes':z.stat().st_size})
native=[]
for name in ['NFM_Driver','NFM_Scanner','NFM_Driver.c','NFM_Scanner.c','NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=B/'NFM_native'/name;q=C/'NFM_native_20261104'/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 native.append(dict(source=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
removed=[]
for name in ['NFM_target','NFM_tmp','NFM_objects','NFM_native']:
 p=B/name
 assert not p.is_symlink()
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(exit=0,admission=a,exports=out,native_cache=native,removed_rebuildable_workspace_paths=removed,own_cache_retained=str(C),sources_and_receipts_retained=True)))
'''.replace('PAYLOAD',repr(json.dumps(items)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFM_EXPORT_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout);(E/'NFM_OBJECT_EXPORTS.json').write_text(json.dumps(x,indent=2)+'\n');print('exported',len(x['exports']),'proof objects/sidecars;',len(x['native_cache']),'native cache files; own cache retained')
