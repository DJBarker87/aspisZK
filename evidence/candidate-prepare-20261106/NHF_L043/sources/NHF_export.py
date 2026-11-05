"""Retain own objects; pin actual first-resolved objects; clean own targets only."""
from pathlib import Path
import json,hashlib,shutil,lzma,subprocess
B=Path(__file__).resolve().parent
assert B.name=='codex-cx-candidate-prepare-20261106'
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
dst=C/'NHF_exports_20261106';dst.mkdir(exist_ok=True);exports=[]
for p in sorted((B/'NHF_objects').iterdir()):
 if not p.is_file():continue
 q=dst/p.name
 if q.exists():assert sha(q)==sha(p),q
 else:shutil.copy2(p,q)
 exports.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
cfg=json.loads((B/'NHF_L042.json').read_text());roots=cfg['env']['LEAN_PATH'].split(':')
mods=[json.loads(l)['module'] for l in (B/'NHF_LOADED_scan.jsonl').read_text().splitlines()]
pins=[]
for mod in mods:
 rel=mod.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,mod
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=mod,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins),sort_keys=True).encode()
(B/'NHF_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NHF_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
removed=[]
for n in ['NHF_target','NHF_extract_target']:
 p=B/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
report=dict(cache_retained=str(dst),exports=exports,selected_closure_modules=len(mods),selected_closure_objects=len(pins),closure_sha256=hashlib.sha256(raw).hexdigest(),removed_own_build_outputs=removed,cache_size=subprocess.check_output(['du','-sh',str(dst)],text=True),disk=subprocess.check_output(['df','-h',str(C)],text=True))
(B/'NHF_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='exports'}))
