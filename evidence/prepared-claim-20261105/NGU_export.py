"""Retain own objects and pin the actual combined closure; remove own build scratch."""
from pathlib import Path
import json,hashlib,shutil,lzma,subprocess
B=Path(__file__).resolve().parent;assert B.name=='codex-cx-prepared-claim-20261105';C=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();exports=[]
for src,dst in [(B/'NGU_objects',C/'NGU_exports_20261105'),(B/'NGU_native',C/'NGU_native_20261105')]:
 dst.mkdir(exist_ok=True)
 for p in src.iterdir():
  if not p.is_file():continue
  q=dst/p.name
  if q.exists():assert sha(q)==sha(p),q
  else:shutil.copy2(p,q)
  exports.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
cfg=json.loads((B/'NGU_L035.json').read_text());roots=list(dict.fromkeys(['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean',str(C/'NGU_exports_20261105')]+cfg['env']['LEAN_PATH'].split(':')));pins=[]
for mod in json.loads((B/'NGU_MODULES.json').read_text()):
 rel=mod.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,mod
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=mod,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins)).encode();(B/'NGU_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGU_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
tool_paths=['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.cargo/bin/cargo','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/leanc'];tools=[dict(path=p,resolved=str(Path(p).resolve()),sha256=sha(Path(p))) for p in tool_paths]
removed=[]
for n in ['NGU_target','NGU_extract_target','NGU_native','NGU_objects','NGU_tmp']:
 p=B/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
report=dict(cache_retained=str(C),exports=exports,selected_closure_objects=len(pins),closure_sha256=hashlib.sha256(raw).hexdigest(),tools=tools,removed_own_build_outputs=removed,cache_size=subprocess.check_output(['du','-sh',str(C)],text=True),disk=subprocess.check_output(['df','-h',str(C)],text=True))
(B/'NGU_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(dict(exports=len(exports),closure_objects=len(pins),cache_size=report['cache_size'],removed_own_build_outputs=removed)))
