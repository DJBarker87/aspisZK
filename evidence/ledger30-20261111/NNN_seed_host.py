"""Copy adopted exports; never mutate a source cache. Run via ssh python3 stdin."""
from pathlib import Path
import json,hashlib,shutil,lzma
B=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNN_20261111');B.mkdir(exist_ok=True)
assert shutil.disk_usage(B).free>=40_000_000_000
M=B.parent/'NNM_20261111';F=Path('/home/dombarker/project-offloads/codex-cx-fin-host-20261108');W=Path('/home/dombarker/project-offloads/codex-cx-libw-host-20261108')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mx=json.loads((M/'NNM_EXPORT.json').read_text());fx=json.loads((F/'NNO_EXPORT.json').read_text());wx=json.loads((W/'NNP_EXPORT.json').read_text())
out=B/'NNN_exports';out.mkdir(exist_ok=True);records=[]
# Full retained ledger29 selection; then verified FIN/NVR overlay; LIBW only fills missing modules.
for root in [Path(mx['export']),Path(fx['export']),Path(wx['export_directory'])]:
 for p in root.iterdir():
  if not p.is_file():continue
  q=out/p.name
  if root==Path(wx['export_directory']) and q.exists():
   records.append(dict(source=str(p),selected=str(q),source_sha256=sha(p),selected_sha256=sha(q),copied=False));continue
  if q.exists():assert sha(q)==sha(p),str(q)
  else:shutil.copy2(p,q)
  records.append(dict(source=str(p),selected=str(q),source_sha256=sha(p),selected_sha256=sha(q),copied=True))
paths=[str(out)]+fx['LEAN_PATH']
# LIBW export has the needed extra NNH owners; retain coherent base before its supplemental path.
paths += [str(Path(wx['export_directory']))]
base=json.loads((W/'NNP_L016.json').read_text())['env']['LEAN_PATH'].split(':')
paths=list(dict.fromkeys(paths+base))
old=json.loads(lzma.open(M/'NNM_CLOSURE_PINS.json.xz').read());checks=[]
for z in old['selected_objects']:
 if not z['path'].endswith('.olean'):continue
 rel=z['module'].replace('.','/')+'.olean';p=next((Path(r)/rel for r in paths if(Path(r)/rel).is_file()),None)
 assert p and sha(p)==z['sha256'],(z,str(p))
 checks.append(dict(module=z['module'],old_sha256=z['sha256'],selected_sha256=sha(p),path=str(p)))
(B/'NNN_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
(B/'NNN_SEED.json').write_text(json.dumps(dict(copies=records,predecessor_objects=checks,basis_export=mx['export'],status='PASS'),indent=1)+'\n')
for n in ['NNN_native','NNN_sources','NNN_tmp']:(B/n).mkdir(exist_ok=True)
S=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 if not(B/n).exists():shutil.copy2(S/n,B/n)
print(json.dumps(dict(status='PASS',copies=len(records),predecessor_objects=len(checks),paths=len(paths))))
