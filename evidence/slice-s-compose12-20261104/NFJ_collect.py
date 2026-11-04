"""Read-only receipts/cache export; no launch or proof replay."""
from pathlib import Path
import subprocess,json,lzma,hashlib,base64
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose12-20261104'
code=f'''from pathlib import Path
import json,lzma,base64,hashlib,shutil
b=Path({B!r});records={{}}
for mode in ['final','fixtures']:
 for p in sorted(b.glob('NEP_'+mode+'_*_REACHABLE.txt')):records[p.name]=p.read_text()
raw=json.dumps(records,sort_keys=True).encode()
cache=b.parent/'codex-cx-slice-s-compose12-cache-20261104/NFJ_final_objects_20261104';cache.mkdir(exist_ok=True);pins=[]
for p in sorted((b/'NFJ_objects').glob('NFJ_*.olean')):
 # Accepted final object only. Failed L002 was replaced by accepted L003.
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server')]:
  if src.exists():
   dst=cache/src.name;shutil.copy2(src,dst);pins.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),bytes=src.stat().st_size))
 src=b/'NFJ_generated'/(p.stem+'.lean');dst=cache/src.name;shutil.copy2(src,dst);pins.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),bytes=src.stat().st_size))
print(json.dumps(dict(reachable_xz_base64=base64.b64encode(lzma.compress(raw,preset=6)).decode(),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),uncompressed_bytes=len(raw),reachable_files=len(records),cache_pins=pins)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);compressed=base64.b64decode(out.pop('reachable_xz_base64'));assert len(compressed)<20*1024*1024
(E/'NFJ_REACHABLE.json.xz').write_bytes(compressed);(E/'NFJ_REACHABLE.json.sha256').write_text(out['uncompressed_sha256']+'\n')
(E/'NFJ_FINAL_CACHE.json').write_text(json.dumps(out,indent=1)+'\n');print('retained',out['reachable_files'],'reachable sets; compressed bytes',len(compressed))
