from pathlib import Path
import json,hashlib,shutil,os
b=Path.cwd();dest=b/'NLA_exports_final_20261109';dest.mkdir(exist_ok=True)
mods=['NLA_RootPrefix','NLA_LaneStep','NLA_DataPrefix','NLA_OwnedData','NLA_AllocationPrefix','NLA_PdaStatus','NLA_LaneAssemble','NLA_COMBINED_IMPORT']
pins=[]
for m in mods:
 for p in sorted((b/'NLA_objects').glob(m+'.*')):
  if not p.is_file():continue
  q=dest/p.name;assert not q.exists();shutil.copy2(p,q)
  pins.append(dict(module=m,source=str(p),path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
assert all(any(p['module']==m and p['path'].endswith('.olean') for p in pins) for m in mods)
r=dict(workspace=str(b),export=str(dest),export_bytes=sum(p['bytes'] for p in pins),files=pins,workspace_bytes=sum(p.stat().st_size for p in b.rglob('*') if p.is_file()),free_bytes=shutil.disk_usage(b).free,CARGO_TARGET_DIR=os.environ['CARGO_TARGET_DIR'],retained=True,cache_deleted=False)
assert r['workspace_bytes']<25_000_000_000
(b/'NLA_EXPORT.json').write_text(json.dumps(r,indent=1)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='files'}))
