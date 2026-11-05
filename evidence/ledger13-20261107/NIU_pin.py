"""Pin the selected combined closure and retain only this job's exports."""
from pathlib import Path
import os,json,lzma,hashlib,shutil
B=Path.cwd();H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
toolroot=Path(os.environ['LEAN_SYSROOT']);toolpins=[]
for p in [toolroot/'bin/lean',toolroot/'bin/lake',toolroot/'bin/leanc',B/'lean-toolchain',B/'S2W_run_host.py',B/'S2W_lean_host.py']:
 toolpins.append(dict(path=str(p),sha256=H(p),bytes=p.stat().st_size))
(B/'NIU_TOOL_PINS.json').write_text(json.dumps(toolpins,indent=1)+'\n')
paths=os.environ['LEAN_PATH'].split(':');loaded=[json.loads(l)for l in(B/'NIU_LOADED_scan.jsonl').read_text().splitlines()];pins=[]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
for row in loaded:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if(Path(root)/rel).is_file()),None);assert p,rel
 for q in[p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=row['module'],path=str(q),sha256=H(q),bytes=q.stat().st_size))
raw=(json.dumps(dict(LEAN_PATH=paths,selected_objects=pins,modules=len(loaded),scan_pass=True),indent=1)+'\n').encode()
(B/'NIU_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NIU_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
prior=json.loads((B/'NIU_PREDECESSOR_PINS.json').read_text())
def key(x):return(x['module'],next(s for s in['.olean.private','.olean.server','.olean','.ir']if x['path'].endswith(s)))
old={key(x):x for x in prior['selected_objects']};new={key(x):x for x in pins}
wrong=[dict(module=k[0],suffix=k[1],old=x,new=new.get(k))for k,x in old.items()if k not in new or new[k]['sha256']!=x['sha256']]
comparison=dict(previous_files=len(old),current_files=len(new),same_predecessor_files=len(old)-len(wrong),mismatches=wrong,added_files=len(set(new)-set(old)),status='PASS'if not wrong else'FINDING')
(B/'NIU_PREDECESSOR_COMPARISON.json').write_text(json.dumps(comparison,indent=1)+'\n');assert not wrong
cache=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIU_20261107/NIU_exports_20261107');cache.mkdir(exist_ok=True);exports=[]
for p in(B/'NIU_objects').rglob('*'):
 if not p.is_file():continue
 q=cache/p.relative_to(B/'NIU_objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert H(q)==H(p)
 else:shutil.copy2(p,q)
 exports.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
(B/'NIU_EXPORT.json').write_text(json.dumps(dict(export=str(cache),files=exports,bytes=sum(x['bytes']for x in exports),cache_retained=True,disk=shutil.disk_usage(B)._asdict()),indent=1)+'\n')
print(json.dumps(dict(status='PASS_PIN_EXPORT',modules=len(loaded),predecessor_files=len(old),exports=len(exports),bytes=sum(x['bytes']for x in exports))))
