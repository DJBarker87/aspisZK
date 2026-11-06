from pathlib import Path
import json,hashlib,os,lzma,shutil
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=os.environ['LEAN_PATH'].split(':')
scan=[json.loads(l) for l in (B/'NJN_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
pins=[]
for r in scan:
 rel=r['module'].replace('.','/')+'.olean'
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=r['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size))
raw=json.dumps(pins,sort_keys=True,separators=(',',':')).encode();(B/'NJN_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NJN_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
mods=['NJN_GuardModel','NJN_AcquireLaws','NJN_DropLaws','NJN_CopyLaws','NJN_GuardComposition','NJN_RoundTrip','NJN_ClockModel','NJN_PdaModel','NJN_CopyInduction','NJN_COMBINED_IMPORT']
rows=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=B/'NJN_objects'/rel;assert p.is_file()
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():rows.append(dict(path=str(q.relative_to(B/'NJN_objects')),sha256=sha(q),bytes=q.stat().st_size))
tree=hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest()
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104')/('NJN_exports_20261108_'+tree[:12]);cache.mkdir(exist_ok=True)
for r in rows:
 p=B/'NJN_objects'/r['path'];q=cache/r['path']
 if q.exists():assert sha(q)==r['sha256']
 else:q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
x=dict(path=str(cache),tree_sha256=tree,files=rows,bytes=sum(r['bytes'] for r in rows),selected_objects=len(pins),closure_pin_raw_sha256=hashlib.sha256(raw).hexdigest(),modules=len(scan),free_bytes=shutil.disk_usage(B).free,target_established=False,new_composed_rows=0)
(B/'NJN_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='files'}))
