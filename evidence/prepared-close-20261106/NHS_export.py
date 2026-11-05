"""Pin first-resolved coherent closure and retain private exports; own cleanup only."""
from pathlib import Path
import json,hashlib,shutil,lzma,subprocess
B=Path(__file__).resolve().parent
assert B.name=='codex-cx-prepared-close-20261106'
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
dst=C/'NHS_exports_20261106';dst.mkdir(exist_ok=True);exports=[]
permitted=set(json.loads((B/'NHS_MODULES.json').read_text()))
for p in sorted((B/'NHS_objects').iterdir()):
 if not p.is_file():continue
 stem=p.name.split('.olean')[0] if '.olean' in p.name else p.stem
 if stem not in permitted:continue
 q=dst/p.name
 if q.exists():assert sha(q)==sha(p),q
 else:shutil.copy2(p,q)
 exports.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
scan=json.loads((B/'NHS_L059.json').read_text());roots=scan['env']['LEAN_PATH'].split(':')
mods=[json.loads(l)['module'] for l in (B/'NHS_LOADED_scan.jsonl').read_text().splitlines()];pins=[]
for mod in mods:
 rel=mod.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,mod
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=mod,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins),sort_keys=True).encode()
(B/'NHS_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NHS_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
restore=[str(dst)]+[r for r in roots if r!=str(B/'NHS_objects')]
(B/'NHS_RESTORE_PATHS.json').write_text(json.dumps(restore,indent=1)+'\n')
toolpaths=[B/'S2W_run_host.py',B/'S2W_lean_host.py',B.parent/'codex-cx-sound-int2-20261025/S2W_run_host.py',B.parent/'codex-cx-sound-int2-20261025/S2W_lean_host.py',B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon',B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')]
tools=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in toolpaths]
assert tools[0]['sha256']==tools[2]['sha256'] and tools[1]['sha256']==tools[3]['sha256']
(B/'NHS_TOOLS.json').write_text(json.dumps(tools,indent=1)+'\n')
bins=[]
for n in ['NHS_Driver','NHS_ProofDriver']:
 p=B/'NHS_native'/n;q=dst/'NHS_audit_bins'/n;q.parent.mkdir(exist_ok=True)
 shutil.copy2(p,q);bins.append(dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size))
removed=[]
for n in ['NHS_target','NHS_objects','NHS_native','NHS_tmp']:
 p=B/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
report=dict(cache_retained=str(dst),exports=exports,audit_binaries=bins,selected_closure_modules=len(mods),selected_closure_objects=len(pins),closure_sha256=hashlib.sha256(raw).hexdigest(),removed_own_build_outputs=removed,cache_size=subprocess.check_output(['du','-sh',str(dst)],text=True),disk=subprocess.check_output(['df','-h',str(C)],text=True),tools_unchanged=True)
(B/'NHS_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['exports']}))
