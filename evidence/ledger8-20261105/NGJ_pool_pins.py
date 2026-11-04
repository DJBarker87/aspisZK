from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger8-20261105'
mods=[json.loads(l)['module'] for l in (E/'NGJ_POOL_LOADED_scan.jsonl').read_text().splitlines()]
code='''from pathlib import Path
import json,lzma,hashlib
b=Path(B);roots=json.loads((b/'NGJ_L030.json').read_text())['env']['LEAN_PATH'].split(':');pins=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,m
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=m,path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins)).encode();(b/'NGJ_POOL_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(b/'NGJ_POOL_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n');print(len(pins))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nmods='+repr(mods)+'\n'+code,text=True,capture_output=True);(E/'NGJ_POOL_PINS_TRANSPORT.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
for n in ['NGJ_POOL_CLOSURE_PINS.json.xz','NGJ_POOL_CLOSURE_PINS.json.sha256']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
print('Pinned Pool closure')
