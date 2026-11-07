"""Pin selected closure and export only this job's objects; never mutate imports."""
from NMF_formal import *
code='''from pathlib import Path
import json,hashlib,shutil
b=Path.cwd();env=json.loads((b/'NMF_ENV.json').read_text());roots=env['LEAN_PATH'].split(':')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
scan=[json.loads(s) for s in (b/'NMF_LOADED_scan.jsonl').read_text().splitlines()]
pins={}
for row in scan:
 rel=row['module'].replace('.','/')+'.olean'
 p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p is not None,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins[str(q)]=dict(module=row['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size)
import lzma
raw=(json.dumps(pins,sort_keys=True,indent=1)+'\\n').encode();(b/'NMF_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(b/'NMF_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
modules=['NMF_WriterRoots','NMF_InputTransport','NMF_ReachedHeader','NMF_GameRoot','NMF_COMBINED_IMPORT','NMF_HypothesisAudit']
out=b/'NMF_exports_20261110';out.mkdir(exist_ok=True);export=[]
for m in modules:
 for p in sorted((b/'NMF_objects').glob(m+'.*')):
  if p.suffix not in ['.olean','.ir','.private','.server']:continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copy2(p,q)
  export.append(dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size))
 src=b/'NMF_generated'/(m+'.lean');q=out/src.name
 if q.exists():assert sha(q)==sha(src)
 else:shutil.copy2(src,q)
 export.append(dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size))
(b/'NMF_EXPORT.json').write_text(json.dumps(dict(directory=str(out),files=export),indent=1)+'\\n')
selected=json.loads((b/'NMF_L010.json').read_text())['deps_fingerprint']['selected_objects']
changed=[p for p,r in selected.items() if sha(Path(p))!=r['sha256']];assert not changed,changed
usage=sum(p.stat().st_size for p in b.rglob('*') if p.is_file());assert usage<30_000_000_000
report=dict(selected_L010_pins_stable=True,selected_L010_objects=len(selected),aeneas_selected_objects=sum('/Aeneas' in p for p in selected),loaded_modules=len(scan),closure_files=len(pins),own_bytes=usage,free_bytes=shutil.disk_usage(b).free,deletions=0)
(b/'NMF_RETENTION.json').write_text(json.dumps(report,indent=1)+'\\n');print(json.dumps(report))
'''
r=run('NMF_L018','inspect','NMF_Finalize',['python3','NMF_finalize_host.py'],{'NMF_finalize_host.py':code,'NMF_ENV.json':(E/'NMF_ENV.json').read_text()})
sys.exit(r['exit_status'])
