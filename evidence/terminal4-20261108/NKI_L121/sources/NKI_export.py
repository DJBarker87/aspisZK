from pathlib import Path
import json,hashlib,shutil,time,subprocess,os
B=Path('/home/dombarker/project-offloads/codex-cx-terminal4-20261108')
X=B/'NKI_exports_20261108';X.mkdir(exist_ok=True)
def pin(q):return dict(path=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest())
gate=json.loads((B/'NKI_GATE_SOURCES.json').read_text())
files=[]
for name in list(gate['passed'])+['NKI_COMBINED_IMPORT']:
 for q in [B/(name+'.lean'),*list((B/'NKI_objects').glob(name+'.*'))]:
  if q.is_file():
   dest=X/q.name
   if dest.exists():assert hashlib.sha256(dest.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest()
   else:shutil.copy2(q,dest)
   files.append(pin(dest))
libs=json.loads((B/'NKI_L090/receipt.json').read_text())['deps_fingerprint']['selected_objects']
for item in libs.values():
 q=Path(item['path']);assert hashlib.sha256(q.read_bytes()).hexdigest()==item['sha256']
usage=sum(q.stat().st_size for q in B.rglob('*')if q.is_file() and not q.is_symlink());assert usage<30_000_000_000
path=json.loads((B/'NKI_L090.json').read_text())['env']['LEAN_PATH']
row=dict(export=str(X),files=files,export_bytes=sum(x['bytes']for x in files),workspace_bytes=usage,free_bytes=shutil.disk_usage(B).free,LEAN_PATH=str(X)+':'+path,CARGO_TARGET_DIR=str(B/'NKI_target'),library_pins=libs,source_revision=json.loads((B/'NKI_L121.json').read_text())['source_revision'],target_established=False,retained=True)
(B/'NKI_EXPORT.json').write_text(json.dumps(row,indent=1));print(json.dumps({k:row[k]for k in ['export','export_bytes','workspace_bytes','free_bytes','target_established']}))
