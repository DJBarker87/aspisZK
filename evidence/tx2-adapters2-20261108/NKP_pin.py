from pathlib import Path
import json,hashlib,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((B/'NKP_PREDECESSOR_PINS.json').read_text());bad=[]
for x in old:
 p=Path(x['path'])
 if not p.is_file() or sha(p)!=x['sha256']:bad.append(x['path'])
roots=os.environ['LEAN_PATH'].split(':');selected=[]
for line in (B/'NKP_LOADED_scan.jsonl').read_text().splitlines():
 x=json.loads(line);mod=x['module'];rel=mod.replace('.','/')+'.olean'
 p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,mod
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():selected.append(dict(module=mod,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
obj=dict(LEAN_PATH=roots,selected_objects=selected,modules=len(set(x['module'] for x in selected)),predecessor_files=len(old),mismatches=bad,scan_pass=not bad)
(B/'NKP_CLOSURE_PINS.json').write_text(json.dumps(obj,indent=1)+'\n')
print(json.dumps(dict(previous_files=len(old),selected_files=len(selected),mismatches=len(bad))))
assert not bad,bad[:3]
