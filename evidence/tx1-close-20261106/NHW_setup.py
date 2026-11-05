"""Own seed setup; caller must have admitted reservation before execution."""
from pathlib import Path
import shutil,json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-tx1-close-20261106')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104')
roots=json.loads((B/'NHW_BASE_PATHS.json').read_text())
dst=C/'NHW_seed_20261106';dst.mkdir(exist_ok=True)
pins=[];replacements={}
for src in [C/'NHS_exports_20261106',C/'NHL_exports_20261106',C/'NHR_exports_20261106']:
 assert src.is_dir(),src
 d=dst/src.name;d.mkdir(exist_ok=True);replacements[str(src)]=str(d)
 for p in sorted(src.iterdir()):
  if not p.is_file() or not any(str(p).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  q=d/p.name
  if not q.exists():shutil.copy2(p,q)
  sha=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==sha
  pins.append(dict(source=str(p),path=str(q),bytes=q.stat().st_size,sha256=sha))
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain']:
 src=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')/name
 if src.exists():shutil.copy2(src,B/name)
paths=[str(B/'NHW_objects'),str(dst/'NHR_exports_20261106'),str(dst/'NHL_exports_20261106')]+[replacements.get(r,r) for r in roots if not r.endswith('/NHL_objects')]
(B/'NHW_SEED.json').write_text(json.dumps(dict(files=pins,bytes=sum(p['bytes'] for p in pins)),indent=1))
(B/'NHW_PATHS.json').write_text(json.dumps(paths,indent=1))
print(json.dumps(dict(seed=json.loads((B/'NHW_SEED.json').read_text()),paths=paths)))
