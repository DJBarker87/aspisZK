"""Read-only final pins, plus deletion of this job's disposable linker temporaries."""
from pathlib import Path
import json,lzma,hashlib,shutil,base64
B=Path('/home/dombarker/project-offloads/codex-cx-fin-host-20261108');P=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=json.loads((B/'NNO_PATHS.json').read_text());pins=json.loads(lzma.open(P/'NNM_CLOSURE_PINS.json.xz').read());errors=[];checked=[]
for z in pins['selected_objects']:
 if z['path'].endswith('.olean'):continue
 suffix=Path(z['path']).name[len(z['module'].split('.')[-1]):]
 rel=z['module'].replace('.','/')+suffix
 p=next((Path(r)/rel for r in paths if(Path(r)/rel).is_file()),None)
 h=sha(p)if p else None
 if h!=z['sha256']:errors.append(dict(expected=z,actual=str(p),actual_sha256=h))
 checked.append(dict(module=z['module'],path=str(p),sha256=h))
side=dict(status='PASS'if not errors else'FAIL',checked=len(checked),errors=errors,selected=checked)
raw=json.dumps(side,indent=1).encode();(B/'NNO_SIDECAR_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NNO_SIDECAR_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
files=[]
for p in sorted((B/'NNO_exports').iterdir()):
 if p.is_file():files.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
export=dict(export=str(B/'NNO_exports'),LEAN_PATH=paths,files=files,retained=True,row_credit='none',coherence_status='ledger29 roots and companions pinned; new combined NFX scan INCOMPLETE',sidecar_status=side['status'],source_revision='see per-scope receipts',new_roots=['FIN_'+str(n)+'.candidate'for n in[240,221,213,333,330]])
(B/'NNO_EXPORT.json').write_text(json.dumps(export,indent=1)+'\n')
removed=[]
for p in (B/'NNO_tmp').glob('*'):
 if p.is_file() and p.suffix in ['.o','.bc']:
  removed.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size));p.unlink()
cleanup=dict(removed=removed,export_retained=True,cache_retained=True,disk=shutil.disk_usage(B)._asdict())
(B/'NNO_CLEANUP.json').write_text(json.dumps(cleanup,indent=1)+'\n')
inputs=[];extra=[]
for p in (B/'NNO_native').glob('*.c'):
 inputs.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size));extra.append(p)
(B/'NNO_LINK_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
names=['NNO_EXPORT.json','NNO_SIDECAR_PINS.json.xz','NNO_SIDECAR_PINS.json.sha256','NNO_CLEANUP.json','NNO_LINK_INPUTS.json']
print(json.dumps({str(p.relative_to(B)):base64.b64encode(p.read_bytes()).decode()for p in [*[B/n for n in names],*extra]}))
