"""Pin the checked selected closure and retain own small export; no cache deletion."""
from pathlib import Path
import os,json,lzma,hashlib,shutil
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();paths=os.environ['LEAN_PATH'].split(':')
loaded=[json.loads(l)for l in(B/'NJY_LOADED_scan.jsonl').read_text().splitlines()];assert all(r['imports_match']and not r['dangling']and not r['duplicate_owners']for r in loaded)
pins=[]
for row in loaded:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if(Path(root)/rel).is_file()),None);assert p,rel
 for q in[p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=row['module'],path=str(q),sha256=H(q),bytes=q.stat().st_size))
raw=(json.dumps(dict(LEAN_PATH=paths,selected_objects=pins,modules=len(loaded),scan_pass=True),indent=1)+'\n').encode();(B/'NJY_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NJY_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
prior=json.loads(lzma.decompress(Path('/home/dombarker/project-offloads/codex-cx-ledger16-20261108/NJW_CLOSURE_PINS.json.xz').read_bytes()))
def key(x):return(x['module'],next(s for s in['.olean.private','.olean.server','.olean','.ir']if x['path'].endswith(s)))
old={key(x):x for x in prior['selected_objects']};new={key(x):x for x in pins};wrong=[dict(module=k[0],suffix=k[1],old=x,new=new.get(k))for k,x in old.items()if k not in new or new[k]['sha256']!=x['sha256']]
(B/'NJY_PREDECESSOR_COMPARISON.json').write_text(json.dumps(dict(previous_files=len(old),current_files=len(new),mismatches=wrong,status='PASS'if not wrong else'FINDING'),indent=1)+'\n');assert not wrong
cache=B/'NJY_exports_20261108';cache.mkdir(exist_ok=True);exports=[]
for p in sorted((B/'NJY_objects').rglob('*')):
 if not p.is_file()or p.name.startswith('NJY_ScanDriver.'):continue
 q=cache/p.relative_to(B/'NJY_objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert H(q)==H(p)
 else:shutil.copy2(p,q)
 name=p.name.split('.')[0];src=B/'NJY_generated'/(name+'.lean')
 exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size,source_sha256=H(src)))
(B/'NJY_EXPORT.json').write_text(json.dumps(dict(export=str(cache),files=exports,bytes=sum(x['bytes']for x in exports),cache_retained=True,CARGO_TARGET_DIR=os.environ['CARGO_TARGET_DIR'],disk=shutil.disk_usage(B)._asdict()),indent=1)+'\n')
print(json.dumps(dict(status='PASS_PIN_EXPORT',modules=len(loaded),predecessor_files=len(old),exports=len(exports),bytes=sum(x['bytes']for x in exports))))
