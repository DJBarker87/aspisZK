from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
selected=json.loads((E/'NFO_CHECKED_SOURCES.json').read_text())
artifacts=json.loads((E/'NFO_INSPECTION_PINS.json').read_text())['artifacts']
code='''from pathlib import Path
import shutil,hashlib,json
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata-20261104')
cache=b.parent/'codex-cx-pool-retdata-cache-20261104';dest=cache/'NFO_final_objects_20261104';dest.mkdir(exist_ok=True)
selected=json.loads(SELECTED);artifacts=json.loads(ARTIFACTS)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for a in artifacts:
 p=Path(a['path']);assert sha(p)==a['sha256'];checks.append(dict(path=str(p),sha256=sha(p)))
out=[]
for n,r in selected.items():
 src=b/'NFO_generated'/(n+'.lean');assert sha(src)==r['source_sha256']
 paths=[src,b/'NFO_objects'/(n+'.olean')]
 for suffix in ['.olean.private','.olean.server','.ir']:
  p=b/'NFO_objects'/(n+suffix)
  if p.exists():paths.append(p)
 for p in paths:
  q=dest/p.name
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copy2(p,q)
  out.append(dict(source=str(p),retained=str(q),sha256=sha(q),size=q.stat().st_size))
native=cache/'NFO_audit_native_20261104';native.mkdir(exist_ok=True)
for name in ['NFO_Driver','NFO_Coherence']:
 p=b/'NFO_native'/name;q=native/name
 if q.exists():assert sha(q)==sha(p)
 else:shutil.copy2(p,q)
 out.append(dict(source=str(p),retained=str(q),sha256=sha(q),size=q.stat().st_size))
# Terminal receipts required for EVERY launch before deleting rebuildable scratch.
for i in range(1,61):assert (b/f'NFO_K{i:03}/receipt.json').exists()
for name in ['NFO_L043','NFO_E001']:assert (b/name/'receipt.json').exists()
removed=[]
for name in ['NFO_target','NFO_ref_target','NFO_tmp','NFO_objects','NFO_native']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(retained=out,elf_recheck=checks,removed_rebuildable_scratch=removed,cache_retained=str(cache),disk_free_bytes=shutil.disk_usage(b).free),indent=1))
'''.replace('SELECTED',repr(json.dumps(selected))).replace('ARTIFACTS',repr(json.dumps(artifacts)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NFO_RETAINED.json').write_text(r.stdout)
print('Retained',len(json.loads(r.stdout)['retained']),'pinned files; cleaned only own rebuildable scratch')
