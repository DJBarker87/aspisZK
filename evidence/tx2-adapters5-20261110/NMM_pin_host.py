from pathlib import Path
import json,hashlib,os
B=Path.cwd();roots=os.environ['LEAN_PATH'].split(':');selected=[]
for line in (B/'NMM_LOADED_scan.jsonl').read_text().splitlines():
 x=json.loads(line);mod=x['module'];rel=mod.replace('.','/')+'.olean'
 p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,mod
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():selected.append(dict(module=mod,path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size))
bad=[]
for seed in json.loads((B/'NMM_SEED_RECHECK.json').read_text())['seeds']:
 for x in seed['pins']:
  p=Path(seed['destination'])/x['relative']
  if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=x['sha256']:bad.append(str(p))
assert not bad,bad[:3]
(B/'NMM_CLOSURE_PINS.json').write_text(json.dumps(dict(LEAN_PATH=roots,selected_objects=selected,modules=len(set(x['module'] for x in selected)),seed_mismatches=bad),indent=1)+'\n')
print(json.dumps(dict(modules=len(set(x['module'] for x in selected)),files=len(selected))))
