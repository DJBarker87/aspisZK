"""Retain only owned checked proof outputs and pin the resolved closure."""
from pathlib import Path
import json,hashlib,lzma,shutil,os
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NGX_seed_20261105');D=C/'NGX_exports_20261105';D.mkdir(exist_ok=True)
manifest=json.loads((B/'NGX_MODULES.json').read_text());paths=manifest['paths'];modules=manifest['closure_modules'];owned=manifest['owned_modules'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=[];copied=[]
for module in modules:
 rel=module.replace('.','/')+'.olean';p=next((Path(root)/rel for root in paths if(Path(root)/rel).is_file()),None);assert p is not None,module
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=module,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
 if module in owned:
  assert str(p).startswith(str(B/'NGX_objects')+'/'),module
  for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if z.is_file():
    dst=D/z.relative_to(B/'NGX_objects');dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.exists():assert sha(dst)==sha(z),dst
    else:shutil.copy2(z,dst)
    copied.append(dict(module=module,source=str(z),destination=str(dst),sha256=sha(dst),bytes=dst.stat().st_size))
raw=json.dumps(pins,indent=1).encode();(B/'NGX_CLOSURE_PINS.json').write_bytes(raw);(B/'NGX_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGX_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
report=dict(status='PASS',destination=str(D),owned_modules=owned,copied=copied,bytes=sum(x['bytes']for x in copied),closure_modules=len(modules),closure_files=len(pins),closure_uncompressed_sha256=hashlib.sha256(raw).hexdigest(),cache_never_deleted=True)
(B/'NGX_EXPORT.json').write_text(json.dumps(report,indent=1));print(json.dumps({k:v for k,v in report.items()if k!='copied'}))
