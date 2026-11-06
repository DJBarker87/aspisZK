from pathlib import Path
import json,lzma,hashlib,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-poseidon-state-20261108')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKG_20261108')
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
inputs=json.loads((B/'NKG_PIN_INPUTS.json').read_text())
for n,v in inputs['inputs'].items():assert sha(B/n)==v,n
oldp=Path(inputs['predecessor']['path']);assert sha(oldp)==inputs['predecessor']['sha256']
old=json.loads(lzma.open(oldp).read());paths=json.loads((B/'NKG_PATHS.json').read_text())
scan=[json.loads(l)for l in(B/'NKG_LOADED_scan.jsonl').read_text().splitlines()]
def key(m,p):
 n=Path(p).name;return(m,n[n.index('.olean'):] if '.olean'in n else '.ir')
prior={key(r['module'],r['path']):r for r in old['selected_objects']}
rows=[]
for r in scan:
 m=r['module'];rel=m.replace('.','/')+'.olean'
 p=next((Path(d)/rel for d in paths if (Path(d)/rel).is_file()),None);assert p,m
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not q.is_file():continue
  h=sha(q);k=key(m,q)
  if k in prior:assert h==prior[k]['sha256'],str(k)
  rows.append(dict(module=m,path=str(q),sha256=h,bytes=q.stat().st_size,inherited=k in prior))
assert set(prior)<=set(key(r['module'],r['path'])for r in rows)
export=C/'NKG_exports_20261108';export.mkdir(exist_ok=True);exported=[]
for r in rows:
 if not r['module'].startswith('NKG_'):continue
 p=Path(r['path']);q=export/p.relative_to(B/'NKG_objects')
 q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==r['sha256']
 else:shutil.copy2(p,q)
 assert sha(q)==r['sha256'];exported.append(dict(source=str(p),path=str(q),sha256=r['sha256'],bytes=q.stat().st_size))
assert len({r['module']for r in rows if r['module'].startswith('NKG_')})==32
seed=json.loads((B/'NKG_SEED.json').read_text())
for r in seed['files']:assert sha(Path(r['destination']))==r['sha256']
D=B/'NKG_L055_validation';D.mkdir(exist_ok=True)
def compressed(n,obj):
 raw=(json.dumps(obj,indent=2)+'\n').encode();(D/(n+'.xz')).write_bytes(lzma.compress(raw));(D/(n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
compressed('NKG_CLOSURE_PINS.json',dict(LEAN_PATH=paths,selected_objects=rows,modules=len(scan),scan_pass=True,inherited_files=len(prior),variants=0))
(D/'NKG_EXPORT.json').write_text(json.dumps(dict(path=str(export),files=exported,bytes=sum(r['bytes']for r in exported),seed_verified=len(seed['files']),seed_bytes=seed['bytes']),indent=2)+'\n')
tools=[Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin')/n for n in ['lean','lake','leanc']]+[B/'S2W_run_host.py',B/'NKG_native/NKG_Driver',B/'NKG_native/NKG_ProofDriver']
(D/'NKG_TOOL_PINS.json').write_text(json.dumps([dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)for p in tools],indent=2)+'\n')
# Only owned rebuildable outputs; retained cache and all source/receipts survive.
removed=[]
for name in ['NKG_target','NKG_objects','NKG_tmp','NKG_native/NKG_Driver','NKG_native/NKG_ProofDriver']:
 p=B/name
 if not p.exists():continue
 assert p.is_relative_to(B) and not p.is_symlink()
 size=sum(q.stat().st_size for q in p.rglob('*')if q.is_file())if p.is_dir()else p.stat().st_size
 if p.is_dir():shutil.rmtree(p)
 else:p.unlink()
 removed.append(dict(path=str(p),bytes=size))
for r in exported:assert sha(Path(r['path']))==r['sha256']
(D/'NKG_HOST_END.json').write_text(json.dumps(dict(removed=removed,removed_bytes=sum(r['bytes']for r in removed),retained_cache=str(C),disk=shutil.disk_usage(B)._asdict(),keys_created_or_touched=False,export_verified=True),indent=2)+'\n')
print(json.dumps(dict(pin='PASS',modules=len(scan),inherited_files=len(prior),variants=0,export_files=len(exported),export_bytes=sum(r['bytes']for r in exported))))
