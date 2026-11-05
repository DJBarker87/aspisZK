"""Pin actual scanned objects, keep only owned proof exports; no shared writes."""
from pathlib import Path
import json,hashlib,lzma,shutil,subprocess
B=Path.cwd();assert B.name=='codex-cx-event-native2-20261107'
C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIF_20261107')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
config=json.loads((B/'NIF_L028.json').read_text());roots=config['env']['LEAN_PATH'].split(':')
scan=[json.loads(l) for l in (B/'NIF_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
pins=[]
for row in scan:
 mod=row['module'];rel=mod.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,mod
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=mod,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins),sort_keys=True).encode()
(B/'NIF_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NIF_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
exports=[];dst=C/'NIF_exports_final_20261107';dst.mkdir(exist_ok=True)
for p in sorted((B/'NIF_objects').glob('NIF_*')):
 if not p.is_file() or not any(p.name.startswith(r['module']+'.') for r in scan if r['module'].startswith('NIF_')):continue
 q=dst/p.name
 if q.exists():assert sha(q)==sha(p)
 else:shutil.copy2(p,q)
 exports.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
restore=[str(dst)]+[r for r in roots if r!=str(B/'NIF_objects')]
(B/'NIF_RESTORE_PATHS.json').write_text(json.dumps(restore,indent=1)+'\n')
# Pin actual selected Aeneas objects in full closure and all launcher/tool bytes.
tools=[]
for p in [B/'S2W_run_host.py',B/'S2W_lean_host.py',B/'lean-toolchain',B/'lakefile.toml',B/'lake-manifest.json',Path(config['env']['LEAN_SYSROOT'])/'bin/lean',B/'NIF_native/NIF_ProofDriver']:
 tools.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
(B/'NIF_TOOLS.json').write_text(json.dumps(tools,indent=1)+'\n')
report=dict(exports=exports,export_bytes=sum(r['bytes'] for r in exports),closure_modules=len(scan),closure_files=len(pins),closure_bytes=sum(r['bytes'] for r in pins),closure_sha256=hashlib.sha256(raw).hexdigest(),selected_Aeneas_files=sum(r['module'].startswith(('Aeneas','AeneasMeta')) for r in pins),cache_retained=str(C),disk=subprocess.check_output(['df','-h',str(C)],text=True))
(B/'NIF_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='exports'}))
