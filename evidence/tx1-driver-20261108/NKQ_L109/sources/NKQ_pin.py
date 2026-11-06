"""Pin the selected combined closure and retain only this job's exports."""
from pathlib import Path
import os,json,lzma,hashlib,shutil
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
toolroot=Path(os.environ['LEAN_SYSROOT']);toolpins=[]
for p in [toolroot/'bin/lean',toolroot/'bin/lake',toolroot/'bin/leanc',B/'lean-toolchain',B/'S2W_run_host.py']:
 toolpins.append(dict(path=str(p),sha256=H(p),bytes=p.stat().st_size))
(B/'NKQ_TOOL_PINS.json').write_text(json.dumps(toolpins,indent=1)+'\n')
paths=os.environ['LEAN_PATH'].split(':');loaded=[json.loads(l)for l in(B/'NKQ_LOADED_scan.jsonl').read_text().splitlines()];pins=[]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
for row in loaded:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if(Path(root)/rel).is_file()),None);assert p,rel
 for q in[p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=row['module'],path=str(q),sha256=H(q),bytes=q.stat().st_size))
raw=(json.dumps(dict(LEAN_PATH=paths,selected_objects=pins,modules=len(loaded),scan_pass=True),indent=1)+'\n').encode()
(B/'NKQ_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NKQ_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
prior=json.loads(lzma.decompress((B/'NKQ_PREDECESSOR_PINS.json.xz').read_bytes()))
def key(x):return(x['module'],next(s for s in['.olean.private','.olean.server','.olean','.ir']if x['path'].endswith(s)))
old={key(x):x for x in prior['selected_objects']};new={key(x):x for x in pins}
wrong=[dict(module=k[0],suffix=k[1],old=x,new=new.get(k))for k,x in old.items()if k not in new or new[k]['sha256']!=x['sha256']]
comparison=dict(previous_files=len(old),current_files=len(new),same_predecessor_files=len(old)-len(wrong),mismatches=wrong,added_files=len(set(new)-set(old)),status='PASS'if not wrong else'FINDING')
(B/'NKQ_PREDECESSOR_COMPARISON.json').write_text(json.dumps(comparison,indent=1)+'\n');assert not wrong
cache=Path('/home/dombarker/project-offloads/codex-cx-tx1-driver-20261108/NKQ_exports_20261108');cache.mkdir(exist_ok=True);exports=[]
for p in(B/'NKQ_objects').rglob('*'):
 if not p.is_file():continue
 q=cache/p.relative_to(B/'NKQ_objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert H(q)==H(p)
 else:shutil.copy2(p,q)
 exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
(B/'NKQ_EXPORT.json').write_text(json.dumps(dict(export=str(cache),files=exports,bytes=sum(x['bytes']for x in exports),cache_retained=True,disk=shutil.disk_usage(B)._asdict()),indent=1)+'\n')
print(json.dumps(dict(status='PASS_PIN_EXPORT',modules=len(loaded),predecessor_files=len(old),exports=len(exports),bytes=sum(x['bytes']for x in exports))))
