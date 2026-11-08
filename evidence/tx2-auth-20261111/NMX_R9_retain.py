from NMX_formal import *
s=lzma.open(E/'NMX_L1383/stdout.log.xz','rt').read();line=next(l.split('NMX_R9_MODULES ',1)[1] for l in s.splitlines() if 'NMX_R9_MODULES ' in l);mods=json.loads(line)
(E/'NMX_R9_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
script='''from pathlib import Path
import json,os,hashlib,lzma,shutil
b=Path.cwd();mods=json.loads((b/'NMX_R9_MODULES.json').read_text());mods.append('NMX_R9_CandidateCombined');roots=[Path(p) for p in os.environ['LEAN_PATH'].split(':')]+[Path(os.environ['LEAN_SYSROOT'])/'lib/lean'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selected=[];exports=[];out=b/'NMX_exports_stage241_20261111';out.mkdir(exist_ok=True)
for m in sorted(set(mods)):
 rel=m.replace('.','/');p=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).is_file()),None);assert p,m
 if m.startswith('RSL_'):assert p.is_relative_to(b/'NMX_R3_canonical_objects'),('non-rev3 RSL owner',m,str(p))
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  row=dict(module=m,path=str(z),sha256=sha(z),bytes=z.stat().st_size);selected.append(row)
  if m.startswith(('NMX_','RSL_','LIBB_','LIB_','NCV_','NDB_','NMS_')):
   suffix=str(z)[len(str(p).removesuffix('.olean')):];q=out/(rel+suffix);q.parent.mkdir(parents=True,exist_ok=True)
   if q.exists():assert sha(q)==row['sha256'],('retained object drift',m)
   else:shutil.copy2(z,q)
   exports.append(dict(row,path=str(q)))
raw=json.dumps(dict(canonical_revision=3,modules=len(set(mods)),LEAN_PATH=os.environ['LEAN_PATH'],objects=selected),separators=(',',':')).encode()
(b/'NMX_R9_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(b/'NMX_R9_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
(b/'NMX_R9_EXPORT.json').write_text(json.dumps(dict(export=str(out),files=exports,loaded_modules=len(set(mods)),loaded_objects=len(selected),deletions=0,disk=shutil.disk_usage(b)._asdict()),indent=1)+'\\n')
print(json.dumps(dict(status='PASS',modules=len(set(mods)),loaded_objects=len(selected),exports=len(exports),deletions=0)))
'''
r=run('NMX_L1391','inspect','retention_r9',['python3','NMX_R9_retain_host.py'],{'NMX_R9_retain_host.py':script,'NMX_R9_MODULES.json':json.dumps(mods)})
assert r['exit_status']==0
z=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['NMX_R9_EXPORT.json','NMX_R9_CLOSURE_PINS.json.xz','NMX_R9_CLOSURE_PINS.json.sha256']}}))
''');assert z.returncode==0
import base64
for n,t in json.loads(z.stdout).items():(E/n).write_bytes(base64.b64decode(t))
