from pathlib import Path
import json,os,hashlib,shutil,lzma
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=json.loads((B/'NMX_R3_MODULES.json').read_text());mods.append('NMX_R3_COMBINED_IMPORT')
roots=[Path(x) for x in os.environ['LEAN_PATH'].split(':')]+[Path(os.environ['LEAN_SYSROOT'])/'lib/lean']
out=B/'NMX_exports_revision3_20261111';out.mkdir(exist_ok=True);selected=[];exports=[]
for m in sorted(set(mods)):
 rel=m.replace('.','/');obj=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).is_file()),None)
 assert obj is not None,('missing object',m)
 if m.startswith('RSL_'):assert obj.is_relative_to(B/'NMX_R3_canonical_objects'),('nonrev3owner',m,str(obj))
 for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if not p.is_file():continue
  row=dict(module=m,path=str(p),bytes=p.stat().st_size,sha256=sha(p));selected.append(row)
  if m.startswith(('NMX_R3_','RSL_','NCV_','NDB_')):
   suffix=str(p)[len(str(obj).removesuffix('.olean')):];q=out/(rel+suffix);q.parent.mkdir(parents=True,exist_ok=True)
   if q.exists():assert sha(q)==sha(p),('retained object drift',q)
   else:shutil.copy2(p,q)
   exports.append(dict(row,path=str(q)))
raw=json.dumps(dict(canonical_revision=3,LEAN_PATH=os.environ['LEAN_PATH'],selected_objects=selected),separators=(',',':')).encode()
(B/'NMX_R3_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NMX_R3_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
x=dict(export=str(out),files=exports,loaded_modules=len(set(mods)),loaded_object_files=len(selected),disk=shutil.disk_usage(B)._asdict(),deletions=0)
(B/'NMX_R3_EXPORT.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(status='PASS',export=str(out),modules=len(set(mods)),files=len(exports))))
