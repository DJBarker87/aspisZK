"""Retain own exports and rehash the inherited coherent selected closure."""
from pathlib import Path
import os,json,hashlib,lzma,shutil
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=[Path(x) for x in os.environ['LEAN_PATH'].split(':')];sysroot=Path(os.environ['LEAN_SYSROOT'])
old=json.loads(lzma.decompress((B/'NMX_PREDECESSOR_PINS.json.xz').read_bytes()))
selected=[];mismatch=[]
for row in old['selected_objects']:
 p=Path(row['path']);suffix=''.join(p.suffixes)
 # Module paths contain dots only in the .olean/private/server suffix.
 rel=row['module'].replace('.','/')+suffix
 q=next((root/rel for root in roots if (root/rel).is_file()),None)
 if q is None:q=p
 h=sha(q)
 if h!=row['sha256']:mismatch.append(dict(module=row['module'],old=str(p),selected=str(q),old_sha256=row['sha256'],sha256=h))
 selected.append(dict(module=row['module'],path=str(q),sha256=h,bytes=q.stat().st_size))
assert not mismatch,mismatch[:5]
passes={}
for p in B.glob('NMX_L*/receipt.json'):
 d=json.loads(p.read_text())
 if d['kind']=='lean' and d['exit_status']==0:passes[d['module']]=d
modules=json.loads((B/'NMX_EXPORT_MODULES.json').read_text());exports=[];srcs=[]
out=B/'NMX_exports_20261111';out.mkdir(exist_ok=True)
for m in modules:
 src=B/'NMX_generated'/(m+'.lean');rc=passes[m]
 assert sha(src)==rc['source_hashes']['NMX_generated/'+m+'.lean'],m
 srcs.append(dict(module=m,path=str(src),sha256=sha(src),accepted_attempt=rc['attempt']))
 obj=B/'NMX_objects'/(m+'.olean');assert obj.is_file(),m
 for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if not p.is_file():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copy2(p,q)
  row=dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size)
  exports.append(row);selected.append(dict(row,path=str(p)))
write=lambda n,d:(B/n).write_text(json.dumps(d,indent=1)+'\n')
write('NMX_EXPORT.json',dict(export=str(out),files=exports,source_inputs=srcs,cache_retained=True))
write('NMX_TOOL_PINS.json',dict(files=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in [sysroot/'bin/lean',sysroot/'bin/lake',sysroot/'bin/leanc',sysroot/'lib/lean/libleanshared.so',B/'S2W_run_host.py',B/'NMX_native/NMX_ProofDriver',B/'NMX_native/NMX_ProofDriver.c',B/'NMX_native/NFA_WALKER.c',B/'NMX_native/NFA_MemoryLimit.c'] if p.is_file()]))
raw=json.dumps(dict(LEAN_PATH=os.environ['LEAN_PATH'],selected_objects=selected,predecessor_hashes_unchanged=True,own_modules=modules)).encode()
(B/'NMX_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NMX_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
write('NMX_RETENTION.json',dict(closure_files=len(selected),inherited_files=len(old['selected_objects']),own_export_files=len(exports),workspace_bytes=sum(p.stat().st_size for p in B.rglob('*') if p.is_file()),disk=shutil.disk_usage(B)._asdict(),deletions=0,scope_overlap=False,source_pins_unchanged=True))
print(json.dumps(dict(inherited_files=len(old['selected_objects']),export_files=len(exports),status='PASS')))
