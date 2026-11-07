from pathlib import Path
import json,lzma,hashlib,shutil,subprocess
B=Path.cwd();raw=lzma.decompress((B/'NMG_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(B/'NMG_CLOSURE_PINS.json.sha256').read_text().strip()
x=json.loads(raw)
for row in x['selected_objects']:
 p=Path(row['path']);assert p.stat().st_size==row['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
export=json.loads((B/'NMG_EXPORT.json').read_text())
for row in export['files']:
 p=Path(row['path']);assert p.stat().st_size==row['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
old=json.loads((B/'NMG_FINAL_HOST.json').read_text())
for n,row in old['tools'].items():
 p=Path(n);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
old.update(dict(selected_objects_rehashed=len(x['selected_objects']),exported_files_rehashed=len(export['files']),own_bytes=int(subprocess.check_output(['du','-sb',str(B)]).split()[0]),disk=shutil.disk_usage(B)._asdict(),retention_pass=True))
assert old['own_bytes']<30_000_000_000 and old['disk']['free']>=40_000_000_000
(B/'NMG_FINAL_HOST.json').write_text(json.dumps(old,indent=1));print(json.dumps(dict(retention=True,selected_objects=len(x['selected_objects']),exported=len(export['files']),own_bytes=old['own_bytes'],free=old['disk']['free'])))
